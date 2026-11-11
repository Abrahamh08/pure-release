//! Allocation-free release planning, without filesystem, build or network effects.
//!
//! Call [`valid`] before applying table-based decisions. Kani checks arbitrary
//! valid topologies and states at [`COMPONENT_COUNT`] components, and compatibility
//! histories of zero through five releases with arbitrary `u64` version triples.
//! Proofs do not establish hardware behavior, dependency discovery, or whether a
//! source change requires a major version bump.
//!
//! Run proofs with Kani 0.68.0: `cargo kani --lib --output-format terse`.
//!
//! Source: <https://github.com/odysseyarm/odyssey/blob/bfb7e416c55b73ddab9a01d31cf4c08e04247943/crates/xtask/src/release_rules.rs>

#![no_std]

mod rules;

pub use rules::{
    COMPONENT_COUNT, Kind, Link, Order, Refusal, Regressed, State, bump_set, deliver,
    oldest_covering, publish_order, state, successor, valid,
};
