#![no_main]

use {
    agave_transaction_view::transaction_view::UnsanitizedTransactionView,
    agave_votor_messages::{
        consensus_message::Block,
        reward_certificate::{NotarRewardCertificate, SkipRewardCertificate},
        wire::{
            ExpectedShredVersion, VersionedWireConsensusMessage, VotePayloadToSign,
            WireBlockCertMessage, WireCertSignature,
        },
    },
    bytes::Bytes,
    libfuzzer_sys::fuzz_target,
    solana_address::Address,
    solana_entry::{
        block_component::{
            BlockComponent, BlockFinalizationCert, BlockFooterV1, BlockHeaderV1, BlockMarkerV1,
            GenesisCertBlockMarker, ParsedBlockComponent, UpdateParentV1, VersionedBlockFooter,
            VersionedBlockHeader, VersionedBlockMarker, VersionedUpdateParent, VotesAggregate,
        },
        block_component_parser::{self, ParseError},
        entry::Entry,
    },
    solana_fee_calculator::FeeCalculator,
    solana_hash::Hash,
    solana_message::{
        compiled_instruction::CompiledInstruction,
        v0::{Message as V0Message, MessageAddressTableLookup},
        Message as LegacyMessage, MessageHeader, VersionedMessage,
    },
    solana_nonce::{
        state::{Data as NonceData, DurableNonce, State as NonceState},
        versions::Versions as NonceVersions,
    },
    solana_signature::Signature,
    solana_transaction::{versioned::VersionedTransaction, Transaction},
    wincode::{config::DefaultConfig, io::Reader, SchemaReadContext},
};

macro_rules! fuzz_roundtrip {
    ($data:expr, $ty:ty) => {
        if let Ok(value) = wincode::deserialize_exact::<$ty>($data) {
            let serialized = wincode::serialize(&value).expect("serialize should succeed");
            assert_eq!($data, serialized, "deserialize -> serialize != orignal_data for type {}\nserialized {:?}\noriginal   {:?}", stringify!($ty), serialized, $data,);
            let roundtrip: $ty =
                wincode::deserialize(&serialized).expect("roundtrip deserialize should succeed");
            assert_eq!(value, roundtrip, "roundtrip failed for {}", stringify!($ty));
        }
    };
}

/// `VersionedWireConsensusMessage` only reads with an `ExpectedShredVersion`
/// context and rejects input whose trailing `u16` shred version does not match.
/// Take the expected version from the last two bytes so well-formed inputs are
/// accepted, and require the reader to be fully consumed to mirror
/// `deserialize_exact`.
fn fuzz_roundtrip_wire_consensus_message(data: &[u8]) {
    let Some(shred_version) = data
        .len()
        .checked_sub(2)
        .map(|i| u16::from_le_bytes([data[i], data[i + 1]]))
    else {
        return;
    };
    let mut reader: &[u8] = data;
    let Ok(value) = <VersionedWireConsensusMessage as SchemaReadContext<
        '_,
        DefaultConfig,
        ExpectedShredVersion,
    >>::get_with_context(ExpectedShredVersion(shred_version), reader.by_ref()) else {
        return;
    };
    if !reader.is_empty() {
        return;
    }
    let serialized = wincode::serialize(&value).expect("serialize should succeed");
    assert_eq!(
        data, serialized,
        "deserialize -> serialize != orignal_data for type \
         VersionedWireConsensusMessage\nserialized {:?}\noriginal   {:?}",
        serialized, data,
    );
    let roundtrip: VersionedWireConsensusMessage =
        wincode::deserialize_with_context(ExpectedShredVersion(shred_version), &serialized)
            .expect("roundtrip deserialize should succeed");
    assert_eq!(
        value, roundtrip,
        "roundtrip failed for VersionedWireConsensusMessage"
    );
}

/// `solana-entry` also ships a hand-written zero-copy parser for block
/// components. It reads the entry framing with wincode readers directly and
/// hands each transaction to `agave-transaction-view`, and it is meant to accept
/// exactly what the derived `BlockComponent` decoder accepts: trailing bytes are
/// ignored and the preallocation limits match. Check that both decoders agree
/// on every input, and that they cover the same bytes for every transaction.
///
/// The one allowed divergence is a transaction the view refuses to frame. The
/// view only parses transactions that could be valid packets (for example it
/// requires at least one signature), and those limits are the view's, not
/// wincode's. Accept that case only when the view rejects the exact transaction
/// the derived decoder produced, so a framing bug cannot hide behind it.
fn fuzz_block_component_parser_equivalence(data: &[u8]) {
    let derived = wincode::deserialize::<BlockComponent>(data);
    let parsed = block_component_parser::parse(Bytes::copy_from_slice(data));
    match (derived, parsed) {
        (Err(_), Err(_)) => {}
        (
            Ok(BlockComponent::EntryBatch(entries)),
            Err(ParseError::Transaction {
                entry_index,
                tx_index,
                error,
            }),
        ) => {
            let tx = entries
                .get(entry_index)
                .and_then(|entry| entry.transactions.get(tx_index))
                .unwrap_or_else(|| {
                    panic!(
                        "parser rejected transaction {tx_index} of entry {entry_index} with \
                         {error:?}, but the derived decode has no such transaction\ninput   \
                         {data:?}"
                    )
                });
            let serialized = wincode::serialize(tx).expect("serialize should succeed");
            assert!(
                UnsanitizedTransactionView::try_new_unsanitized_from_prefix(serialized.as_slice())
                    .is_err(),
                "parser rejected transaction {tx_index} of entry {entry_index} with {error:?}, \
                 but the transaction view accepts that transaction on its own\ntx      \
                 {tx:?}\ninput   {data:?}"
            );
        }
        (
            Ok(BlockComponent::BlockMarker(derived)),
            Ok(ParsedBlockComponent::BlockMarker(parsed)),
        ) => {
            assert_eq!(
                derived, parsed,
                "block marker mismatch between derived decode and parser"
            );
        }
        (Ok(BlockComponent::EntryBatch(entries)), Ok(ParsedBlockComponent::EntryBatch(views))) => {
            assert_eq!(
                entries.len(),
                views.len(),
                "entry count mismatch between derived decode and parser"
            );
            for (index, (entry, view)) in entries.iter().zip(&views).enumerate() {
                assert_eq!(
                    entry.num_hashes, view.num_hashes,
                    "entry {index}: num_hashes mismatch"
                );
                assert_eq!(entry.hash, view.hash, "entry {index}: hash mismatch");
                assert_eq!(
                    entry.transactions.len(),
                    view.transactions.len(),
                    "entry {index}: transaction count mismatch"
                );
                for (tx_index, (tx, tx_view)) in entry
                    .transactions
                    .iter()
                    .zip(&view.transactions)
                    .enumerate()
                {
                    let serialized = wincode::serialize(tx).expect("serialize should succeed");
                    assert_eq!(
                        serialized,
                        tx_view.data(),
                        "entry {index} transaction {tx_index}: derived decode and transaction \
                         view cover different bytes"
                    );
                }
            }
        }
        (derived, parsed) => panic!(
            "derived BlockComponent decode and block_component_parser::parse disagree\nderived \
             {derived:?}\nparsed  {parsed:?}\ninput   {data:?}"
        ),
    }
}

fuzz_target!(|data: &[u8]| {
    fuzz_roundtrip!(data, Address);
    fuzz_roundtrip!(data, Hash);
    fuzz_roundtrip!(data, DurableNonce);
    fuzz_roundtrip!(data, Signature);
    fuzz_roundtrip!(data, FeeCalculator);
    fuzz_roundtrip!(data, MessageHeader);
    fuzz_roundtrip!(data, CompiledInstruction);
    fuzz_roundtrip!(data, MessageAddressTableLookup);
    fuzz_roundtrip!(data, NonceData);
    fuzz_roundtrip!(data, NonceState);
    fuzz_roundtrip!(data, NonceVersions);
    fuzz_roundtrip!(data, LegacyMessage);
    fuzz_roundtrip!(data, V0Message);
    fuzz_roundtrip!(data, VersionedMessage);
    fuzz_roundtrip!(data, Transaction);
    fuzz_roundtrip!(data, VersionedTransaction);
    fuzz_roundtrip!(data, Entry);
    fuzz_roundtrip!(data, SkipRewardCertificate);
    fuzz_roundtrip!(data, NotarRewardCertificate);
    fuzz_roundtrip!(data, Block);
    fuzz_roundtrip!(data, WireCertSignature);
    fuzz_roundtrip!(data, WireBlockCertMessage);
    fuzz_roundtrip!(data, VotePayloadToSign);
    fuzz_roundtrip_wire_consensus_message(data);
    fuzz_roundtrip!(data, BlockFooterV1);
    fuzz_roundtrip!(data, BlockHeaderV1);
    fuzz_roundtrip!(data, UpdateParentV1);
    fuzz_roundtrip!(data, GenesisCertBlockMarker);
    fuzz_roundtrip!(data, BlockFinalizationCert);
    fuzz_roundtrip!(data, VotesAggregate);
    fuzz_roundtrip!(data, VersionedBlockFooter);
    fuzz_roundtrip!(data, VersionedBlockHeader);
    fuzz_roundtrip!(data, VersionedUpdateParent);
    fuzz_roundtrip!(data, BlockMarkerV1);
    fuzz_roundtrip!(data, VersionedBlockMarker);
    fuzz_roundtrip!(data, BlockComponent);
    fuzz_block_component_parser_equivalence(data);
});
