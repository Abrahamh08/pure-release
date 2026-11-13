//! Allocation-free release planning, without filesystem, build or network effects.
//!
//! Call [`valid`] before applying table-based decisions. Verus verifies the seven
//! release properties for arbitrary table sizes and compatibility-history lengths.
//! Kani independently checks arbitrary valid topologies and states at
//! [`COMPONENT_COUNT`] components, and histories of zero through five releases.
//! Both cover arbitrary `u64` version triples.
//! Proofs do not establish hardware behavior, dependency discovery, or whether a
//! source change requires a major version bump.
//!
//! Run Verus with `tools/verify-verus.sh` and the pinned verifier on `PATH`.
//! The gate rejects unproved assumptions and skipped executable bodies.
//! Checked helper proofs reuse `vstd`.
//! Run bounded proofs with Kani 0.68.0: `cargo kani --lib --output-format terse`.
//!
//! Source: <https://github.com/odysseyarm/odyssey/blob/bfb7e416c55b73ddab9a01d31cf4c08e04247943/crates/xtask/src/release_rules.rs>

#![no_std]
#![cfg_attr(verus_only, feature(proc_macro_hygiene))]

mod rules;

pub use rules::{
    COMPONENT_COUNT, Kind, Link, Order, Refusal, Regressed, State, bump_set, deliver,
    oldest_covering, publish_order, state, successor, valid,
};
