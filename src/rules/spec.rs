//! What the executable rules are verified against, for tables of any size.
//!
//! These definitions are the trusted part: a proof only shows that the code
//! agrees with them. `theorems.rs` derives the release properties from them.

use vstd::prelude::*;

use super::{Kind, Link, State};

verus! {

/// Every part names an application, and no application is bumped by name only.
pub open spec fn valid_table(table: Seq<Link>) -> bool {
    forall|i: int|
        0 <= i < table.len() ==> match (#[trigger] table[i]).kind {
            Kind::Part { app } => app < table.len() && table[app as int].kind is App,
            Kind::App => !table[i].manual,
            Kind::Other => true,
        }
}

pub open spec fn is_part_of(table: Seq<Link>, part: int, app: int) -> bool {
    table[part].kind matches Kind::Part { app: named } && named == app
}

/// Component `i` is headed to units: ahead of its tag, about to be bumped, or
/// ahead of what its application's newest entry carries.
pub open spec fn outgoing(table: Seq<Link>, states: Seq<State>, behind: Seq<bool>, i: int) -> bool {
    states[i] is Ready || (states[i] is NeedsBump && !table[i].manual) || behind[i]
}

pub open spec fn forces(
    table: Seq<Link>,
    states: Seq<State>,
    behind: Seq<bool>,
    part: int,
    app: int,
) -> bool {
    &&& 0 <= part < table.len()
    &&& is_part_of(table, part, app)
    &&& outgoing(table, states, behind, part)
}

pub open spec fn forcing_below(
    table: Seq<Link>,
    states: Seq<State>,
    behind: Seq<bool>,
    app: int,
    bound: int,
) -> bool {
    exists|part: int| part < bound && #[trigger] forces(table, states, behind, part, app)
}

/// Delivery makes application `app` release.
pub open spec fn forced(table: Seq<Link>, states: Seq<State>, behind: Seq<bool>, app: int) -> bool {
    states[app] is Current && forcing_below(table, states, behind, app, table.len() as int)
}

pub open spec fn names<const N: usize>(named: Option<&[bool; N]>) -> Option<Seq<bool>> {
    match named {
        Some(named) => Some(named@),
        None => None,
    }
}

/// `bump` is asked to raise component `i` itself.
pub open spec fn asked(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
) -> bool {
    match named {
        Some(named) => named[i],
        None => states[i] is NeedsBump && !table[i].manual,
    }
}

pub open spec fn carries_asked_below(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    app: int,
    bound: int,
) -> bool {
    exists|part: int|
        0 <= part < bound && #[trigger] is_part_of(table, part, app) && asked(
            table,
            states,
            named,
            part,
        )
}

/// `bump` raises component `i`.
pub open spec fn bumped(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
) -> bool {
    !(states[i] is Ready) && (asked(table, states, named, i) || carries_asked_below(
        table,
        states,
        named,
        i,
        table.len() as int,
    ))
}

/// `publish` is asked to release component `i`.
pub open spec fn chosen(states: Seq<State>, named: Option<Seq<bool>>, i: int) -> bool {
    match named {
        Some(named) => named[i],
        None => states[i] is Ready,
    }
}

pub open spec fn not_ready(states: Seq<State>, named: Option<Seq<bool>>, i: int) -> bool {
    chosen(states, named, i) && !(states[i] is Ready)
}

pub open spec fn no_carrier(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
) -> bool {
    chosen(states, named, i) && (table[i].kind matches Kind::Part { app } && !(states[app as int] is Ready))
}

pub open spec fn rank_of(kind: Kind) -> int {
    match kind {
        Kind::Part { .. } => 0,
        Kind::App => 1,
        Kind::Other => 2,
    }
}

/// Component `a` is released before component `b`.
pub open spec fn before(table: Seq<Link>, a: int, b: int) -> bool {
    rank_of(table[a].kind) < rank_of(table[b].kind) || (rank_of(table[a].kind) == rank_of(
        table[b].kind,
    ) && a < b)
}

/// Parts, then applications, then the rest, each by table index. Strict, so
/// no component appears twice.
pub open spec fn in_release_order(table: Seq<Link>, order: Seq<usize>) -> bool {
    forall|p: int, q: int|
        0 <= p < q < order.len() ==> before(table, #[trigger] order[p] as int, #[trigger] order[q] as int)
}

/// `publish` releases exactly the chosen components, in release order.
pub open spec fn releases(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    order: Seq<usize>,
) -> bool {
    &&& forall|p: int| 0 <= p < order.len() ==> #[trigger] order[p] < table.len()
    &&& forall|i: int|
        0 <= i < table.len() ==> (order.contains(i as usize) <==> #[trigger] chosen(states, named, i))
    &&& in_release_order(table, order)
}

/// Lexicographic `version >= want`.
pub open spec fn at_least_spec(version: [u64; 3], want: [u64; 3]) -> bool {
    version[0] > want[0] || (version[0] == want[0] && (version[1] > want[1] || (version[1]
        == want[1] && version[2] >= want[2])))
}

/// Release `i` speaks at least `want`.
pub open spec fn covers(want: [u64; 3], speaks: Seq<Option<[u64; 3]>>, i: int) -> bool {
    speaks[i] matches Some(version) && at_least_spec(version, want)
}

}
