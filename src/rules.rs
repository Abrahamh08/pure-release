//! Release planning over validated fixed-size component tables.

use core::cmp::Ordering;

#[cfg(verus_only)]
use vstd::prelude::*;

#[cfg(verus_only)]
mod lemmas;
#[cfg(verus_only)]
mod spec;
#[cfg(verus_only)]
mod theorems;

#[cfg(verus_only)]
use lemmas::{
    lemma_carrying_step, lemma_forcing_step, lemma_parts_carry_nothing, lemma_release_next,
};
#[cfg(verus_only)]
use spec::{
    asked, at_least_spec, bumped, carries_asked_below, covers, forced, forces, forcing_below,
    in_release_order, is_part_of, names, no_carrier, not_ready, rank_of, releases, valid_table,
};

/// Verus proof blocks are erased from ordinary builds.
#[cfg(not(verus_only))]
macro_rules! proof {
    ($($tokens:tt)*) => {};
}

/// Ghost declarations shared by later proof blocks are erased as well.
#[cfg(not(verus_only))]
macro_rules! proof_decl {
    ($($tokens:tt)*) => {};
}

/// Component table size covered by the exhaustive Kani harnesses. The Verus
/// proofs hold for every size.
pub const COMPONENT_COUNT: usize = 11;

#[cfg_attr(verus_only, verus_verify, derive(Structural))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum State {
    /// Released as it is.
    Current,
    /// Changed since its tag under the tag's version.
    NeedsBump,
    /// The source is ahead of the newest tag, or was never released.
    Ready,
}

/// The source version is below one already released.
#[cfg_attr(verus_only, verus_verify, derive(Structural))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Regressed;

/// `ahead` orders the source version against the newest tag's, and is `None`
/// for a component that has no tag.
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        result is Err <==> ahead == Some(Ordering::Less),
        ahead is None || ahead == Some(Ordering::Greater) ==> result == Ok::<State, Regressed>(State::Ready),
        ahead == Some(Ordering::Equal) && changed ==> result == Ok::<State, Regressed>(State::NeedsBump),
        ahead == Some(Ordering::Equal) && !changed ==> result == Ok::<State, Regressed>(State::Current),
))]
pub fn state(ahead: Option<Ordering>, changed: bool) -> Result<State, Regressed> {
    match ahead {
        None | Some(Ordering::Greater) => Ok(State::Ready),
        Some(Ordering::Less) => Err(Regressed),
        Some(Ordering::Equal) if changed => Ok(State::NeedsBump),
        Some(Ordering::Equal) => Ok(State::Current),
    }
}

#[cfg_attr(verus_only, verus_verify, derive(Structural))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Kind {
    /// A net core or bootloader. Units receive it through the manifest entries
    /// of the application at this table index.
    Part {
        app: usize,
    },
    App,
    Other,
}

#[cfg_attr(verus_only, verus_verify, derive(Structural))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Link {
    pub kind: Kind,
    /// Bumped only by name.
    pub manual: bool,
}

/// Every part names an application, and no application is bumped by name only:
/// it could then stay behind a part it has to deliver. Every other function
/// here requires a valid table.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        result == valid_table(table@),
))]
pub fn valid<const N: usize>(table: &[Link; N]) -> bool {
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < i ==> match (#[trigger] table@[j]).kind {
                Kind::Part { app } => app < N && table@[app as int].kind is App,
                Kind::App => !table@[j].manual,
                Kind::Other => true,
            },
    ))]
    for i in 0..N {
        match table[i].kind {
            Kind::Part { app } => {
                if app >= N || table[app].kind != Kind::App {
                    return false;
                }
            }
            Kind::App => {
                if table[i].manual {
                    return false;
                }
            }
            Kind::Other => {}
        }
    }
    true
}

/// A unit only receives a part through an application entry that carries it, so
/// a part on its way out makes its application release too. `behind[i]` says
/// part `i`'s counter is above the one its application's newest entry carries.
/// Returns, for each application made to release, the part that forces it.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    requires
        valid_table(table@),
    ensures
        forall|app: int| 0 <= app < N ==> #[trigger] final(states)@[app] == (
            if forced(table@, old(states)@, behind@, app) { State::NeedsBump } else { old(states)@[app] }),
        forall|app: int| 0 <= app < N ==> (
            #[trigger] result@[app] is Some <==> forced(table@, old(states)@, behind@, app)),
        forall|app: int| 0 <= app < N ==> (#[trigger] result@[app] matches Some(part) ==>
            forces(table@, old(states)@, behind@, part as int, app)
            && !forcing_below(table@, old(states)@, behind@, app, part as int)),
))]
pub fn deliver<const N: usize>(
    table: &[Link; N],
    states: &mut [State; N],
    behind: &[bool; N],
) -> [Option<usize>; N] {
    let mut forced: [Option<usize>; N] = [None; N];
    #[cfg_attr(verus_only, verus_spec(
        invariant
            valid_table(table@),
            forall|k: int| 0 <= k < N && !(table@[k].kind is App) ==> #[trigger] states@[k] == old(states)@[k],
            forall|app: int| 0 <= app < N ==> #[trigger] states@[app] == (
                if old(states)@[app] is Current && forcing_below(table@, old(states)@, behind@, app, i as int) {
                    State::NeedsBump
                } else {
                    old(states)@[app]
                }),
            forall|app: int| 0 <= app < N ==> (#[trigger] forced@[app] is Some <==>
                old(states)@[app] is Current && forcing_below(table@, old(states)@, behind@, app, i as int)),
            forall|app: int| 0 <= app < N ==> (#[trigger] forced@[app] matches Some(part) ==>
                part < i
                && forces(table@, old(states)@, behind@, part as int, app)
                && !forcing_below(table@, old(states)@, behind@, app, part as int)),
    ))]
    for i in 0..N {
        proof! {
            assert forall|app: int| 0 <= app < N implies
                #[trigger] forcing_below(table@, old(states)@, behind@, app, i + 1)
                    == (forcing_below(table@, old(states)@, behind@, app, i as int)
                        || forces(table@, old(states)@, behind@, i as int, app)) by {
                lemma_forcing_step(table@, old(states)@, behind@, app, i as int);
            }
        }
        let Kind::Part { app } = table[i].kind else {
            continue;
        };
        let on_its_way = match states[i] {
            State::Ready => true,
            State::NeedsBump => !table[i].manual,
            State::Current => false,
        };
        if (on_its_way || behind[i]) && states[app] == State::Current {
            states[app] = State::NeedsBump;
            forced[app] = Some(i);
        }
    }
    forced
}

/// The components `bump` raises: the `named` ones, or without names every
/// changed one that is not bumped by name only; plus the application of each
/// part among them. A component already ahead of its tag is never raised again.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    requires
        valid_table(table@),
    ensures
        forall|i: int| 0 <= i < N ==> #[trigger] result@[i] == bumped(table@, states@, names(named), i),
))]
pub fn bump_set<const N: usize>(
    table: &[Link; N],
    states: &[State; N],
    named: Option<&[bool; N]>,
) -> [bool; N] {
    let mut wanted = [false; N];
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] wanted@[j] == asked(table@, states@, names(named), j),
    ))]
    for i in 0..N {
        wanted[i] = match named {
            Some(named) => named[i],
            None => states[i] == State::NeedsBump && !table[i].manual,
        };
    }
    #[cfg_attr(verus_only, verus_spec(
        invariant
            valid_table(table@),
            forall|j: int| 0 <= j < N ==> #[trigger] wanted@[j] == (
                asked(table@, states@, names(named), j)
                || carries_asked_below(table@, states@, names(named), j, i as int)),
    ))]
    for i in 0..N {
        proof! {
            assert forall|app: int| 0 <= app < N implies
                #[trigger] carries_asked_below(table@, states@, names(named), app, i + 1)
                    == (carries_asked_below(table@, states@, names(named), app, i as int)
                        || (is_part_of(table@, i as int, app) && asked(table@, states@, names(named), i as int))) by {
                lemma_carrying_step(table@, states@, names(named), app, i as int);
            }
            if !(table@[i as int].kind is App) {
                lemma_parts_carry_nothing(table@, states@, names(named), i as int, i as int);
            }
        }
        let kind = table[i].kind;
        match kind {
            Kind::Part { app } if wanted[i] => wanted[app] = true,
            _ => {}
        }
    }
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] wanted@[j] == bumped(table@, states@, names(named), j),
            forall|j: int| i <= j < N ==> #[trigger] wanted@[j] == (
                asked(table@, states@, names(named), j)
                || carries_asked_below(table@, states@, names(named), j, N as int)),
    ))]
    for i in 0..N {
        if states[i] == State::Ready {
            wanted[i] = false;
        }
    }
    wanted
}

#[cfg_attr(verus_only, verus_verify, derive(Structural))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refusal {
    /// The named component is not ahead of its tag.
    NotReady(usize),
    /// No release of `app` is on its way to deliver `part`, so no unit would
    /// ever be offered it.
    NoCarrier { part: usize, app: usize },
}

/// Table indices in the order `publish` releases them.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, Debug)]
pub struct Order<const N: usize> {
    items: [usize; N],
    len: usize,
}

impl<const N: usize> Order<N> {
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            result@ == self@,
    ))]
    pub fn as_slice(&self) -> &[usize] {
        proof! {
            use_type_invariant(self);
        }
        &self.items[..self.len]
    }
}

#[cfg(verus_only)]
verus! {

impl<const N: usize> Order<N> {
    #[verifier::type_invariant]
    pub closed spec fn well_formed(self) -> bool {
        self.len <= N
    }

    /// The released indices, in order.
    pub closed spec fn view(self) -> Seq<usize> {
        self.items@.subrange(0, self.len as int)
    }
}

}

#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        result == rank_of(kind),
))]
fn rank(kind: Kind) -> u8 {
    match kind {
        Kind::Part { .. } => 0,
        Kind::App => 1,
        Kind::Other => 2,
    }
}

/// The components `publish` releases: the `named` ones, or without names every
/// one ahead of its tag. Parts come first, because an application's manifest
/// entry hashes the published net core and bootloader.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    requires
        valid_table(table@),
    ensures
        match result {
            Ok(order) => {
                &&& forall|i: int| 0 <= i < N ==> !not_ready(states@, names(named), i)
                &&& forall|i: int| 0 <= i < N ==> !no_carrier(table@, states@, names(named), i)
                &&& releases(table@, states@, names(named), order@)
            },
            Err(Refusal::NotReady(i)) => {
                &&& i < N
                &&& not_ready(states@, names(named), i as int)
                &&& forall|j: int| 0 <= j < i ==> !not_ready(states@, names(named), j)
            },
            Err(Refusal::NoCarrier { part, app }) => {
                &&& part < N
                &&& is_part_of(table@, part as int, app as int)
                &&& no_carrier(table@, states@, names(named), part as int)
                &&& forall|j: int| 0 <= j < N ==> !not_ready(states@, names(named), j)
                &&& forall|j: int| 0 <= j < part ==> !no_carrier(table@, states@, names(named), j)
            },
        },
))]
pub fn publish_order<const N: usize>(
    table: &[Link; N],
    states: &[State; N],
    named: Option<&[bool; N]>,
) -> Result<Order<N>, Refusal> {
    let mut chosen = [false; N];
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] chosen@[j] == spec::chosen(states@, names(named), j),
            forall|j: int| 0 <= j < i ==> !not_ready(states@, names(named), j),
    ))]
    for i in 0..N {
        chosen[i] = match named {
            Some(named) => named[i],
            None => states[i] == State::Ready,
        };
        if chosen[i] && states[i] != State::Ready {
            return Err(Refusal::NotReady(i));
        }
    }
    #[cfg_attr(verus_only, verus_spec(
        invariant
            valid_table(table@),
            forall|j: int| 0 <= j < i ==> !no_carrier(table@, states@, names(named), j),
    ))]
    for i in 0..N {
        let kind = table[i].kind;
        match kind {
            Kind::Part { app } if chosen[i] && states[app] != State::Ready => {
                return Err(Refusal::NoCarrier { part: i, app });
            }
            _ => {}
        }
    }
    let mut items = [0usize; N];
    let mut len = 0usize;
    #[cfg_attr(verus_only, verus_spec(
        invariant
            len <= N,
            forall|p: int| 0 <= p < len ==> #[trigger] items@[p] < N,
            forall|p: int| 0 <= p < len ==> spec::chosen(states@, names(named), #[trigger] items@[p] as int),
            forall|p: int| 0 <= p < len ==> rank_of(table@[#[trigger] items@[p] as int].kind) < wave,
            forall|j: int| 0 <= j < N && spec::chosen(states@, names(named), j) && rank_of(table@[j].kind) < wave
                ==> items@.subrange(0, len as int).contains(j as usize),
            in_release_order(table@, items@.subrange(0, len as int)),
    ))]
    for wave in 0..3 {
        #[cfg_attr(verus_only, verus_spec(
            invariant
                0 <= wave < 3,
                len <= N,
                forall|j: int| 0 <= j < N ==> #[trigger] chosen@[j] == spec::chosen(states@, names(named), j),
                forall|p: int| 0 <= p < len ==> #[trigger] items@[p] < N,
                forall|p: int| 0 <= p < len ==> spec::chosen(states@, names(named), #[trigger] items@[p] as int),
                forall|p: int| 0 <= p < len ==> {
                    let at = #[trigger] items@[p] as int;
                    rank_of(table@[at].kind) < wave || (rank_of(table@[at].kind) == wave && at < i)
                },
                forall|j: int| 0 <= j < N && spec::chosen(states@, names(named), j)
                    && (rank_of(table@[j].kind) < wave || (rank_of(table@[j].kind) == wave && j < i))
                    ==> items@.subrange(0, len as int).contains(j as usize),
                in_release_order(table@, items@.subrange(0, len as int)),
        ))]
        for i in 0..N {
            if chosen[i] && rank(table[i].kind) == wave {
                proof_decl! {
                    let ghost released = items@.subrange(0, len as int);
                }
                proof! {
                    lemma_release_next(table@, released, i, wave as int);
                }
                items[len] = i;
                len += 1;
                proof! {
                    assert(items@.subrange(0, len as int) =~= released.push(i));
                }
            }
        }
    }
    Ok(Order { items, len })
}

/// The next counter, only when it stays within the component's representation.
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        result == (if value < maximum { Some((value + 1) as u64) } else { None::<u64> }),
))]
pub fn successor(value: u64, maximum: u64) -> Option<u64> {
    match value.checked_add(1) {
        Some(next) if next <= maximum => Some(next),
        _ => None,
    }
}

/// Lexicographic `version >= want`, spelled out because Verus has no
/// specification for array comparison.
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        result == at_least_spec(version, want),
))]
fn at_least(version: [u64; 3], want: [u64; 3]) -> bool {
    if version[0] != want[0] {
        return version[0] > want[0];
    }
    if version[1] != want[1] {
        return version[1] > want[1];
    }
    version[2] >= want[2]
}

/// Index of the oldest Desktop release from which every later one speaks at
/// least `want`. `speaks` is oldest first; `None` marks a release without the
/// wire constant.
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        match result {
            Some(floor) => {
                &&& floor < speaks@.len()
                &&& forall|later: int| floor <= later < speaks@.len() ==> covers(want, speaks@, later)
                &&& floor == 0 || !covers(want, speaks@, floor - 1)
            },
            None => speaks@.len() == 0 || !covers(want, speaks@, speaks@.len() - 1),
        },
))]
pub fn oldest_covering(want: [u64; 3], speaks: &[Option<[u64; 3]>]) -> Option<usize> {
    let mut floor = None;
    let mut i = speaks.len();
    #[cfg_attr(verus_only, verus_spec(
        invariant
            i <= speaks@.len(),
        invariant_except_break
            forall|later: int| i <= later < speaks@.len() ==> covers(want, speaks@, later),
            floor == (if i < speaks@.len() { Some(i) } else { None::<usize> }),
        ensures
            match floor {
                Some(floor) => {
                    &&& floor < speaks@.len()
                    &&& forall|later: int| floor <= later < speaks@.len() ==> covers(want, speaks@, later)
                    &&& floor == 0 || !covers(want, speaks@, floor - 1)
                },
                None => speaks@.len() == 0 || !covers(want, speaks@, speaks@.len() - 1),
            },
        decreases i,
    ))]
    while i > 0 {
        i -= 1;
        let spoken = speaks[i];
        match spoken {
            Some(version) if at_least(version, want) => floor = Some(i),
            _ => break,
        }
    }
    floor
}

#[cfg(kani)]
mod proofs {
    use super::*;

    const N: usize = COMPONENT_COUNT;
    /// `#[kani::unwind]` takes a literal: one more than the longest loop.
    const _: () = {
        assert!(N + 1 == 12);
    };
    const DESKTOPS: usize = 5;

    fn any_table() -> [Link; N] {
        let table: [Link; N] = kani::any();
        kani::assume(valid(&table));
        table
    }

    /// What `plan` hands to `bump` and `publish`: any states, after delivery.
    fn any_plan(table: &[Link; N]) -> ([State; N], [bool; N]) {
        let mut states: [State; N] = kani::any();
        let behind: [bool; N] = kani::any();
        deliver(table, &mut states, &behind);
        (states, behind)
    }

    fn on_its_way(table: &[Link; N], states: &[State; N], i: usize) -> bool {
        states[i] == State::Ready || (states[i] == State::NeedsBump && !table[i].manual)
    }

    #[kani::proof]
    fn a_changed_component_is_never_current_and_a_regression_is_refused() {
        let a: u8 = kani::any();
        let b: u8 = kani::any();
        let ahead = if kani::any() { Some(a.cmp(&b)) } else { None };
        let changed: bool = kani::any();
        let state = state(ahead, changed);
        assert_eq!(state.is_err(), ahead == Some(Ordering::Less));
        if changed {
            assert!(state != Ok(State::Current));
        }
        if ahead == Some(Ordering::Equal) && !changed {
            assert!(state == Ok(State::Current));
        }
        if ahead.is_none() || ahead == Some(Ordering::Greater) {
            assert!(state == Ok(State::Ready));
        }
    }

    #[kani::proof]
    #[kani::unwind(12)]
    fn delivery_leaves_no_outgoing_part_without_a_releasing_application() {
        let table = any_table();
        let before: [State; N] = kani::any();
        let behind: [bool; N] = kani::any();
        let mut states = before;
        let forced = deliver(&table, &mut states, &behind);
        for i in 0..N {
            if let Kind::Part { app } = table[i].kind {
                if on_its_way(&table, &states, i) || behind[i] {
                    assert!(states[app] != State::Current);
                }
            }
            let raised = before[i] == State::Current && states[i] == State::NeedsBump;
            assert!(states[i] == before[i] || (raised && table[i].kind == Kind::App));
            assert_eq!(forced[i].is_some(), raised);
        }
        let mut again = states;
        deliver(&table, &mut again, &behind);
        assert!(again == states);
    }

    #[kani::proof]
    #[kani::unwind(12)]
    fn one_bump_leaves_nothing_to_bump_and_publish_then_accepts_everything_ready() {
        let table = any_table();
        let (states, behind) = any_plan(&table);
        let set = bump_set(&table, &states, None);
        let mut after = states;
        let mut behind_after = behind;
        for i in 0..N {
            if states[i] == State::NeedsBump && !table[i].manual {
                assert!(set[i]);
            }
            if set[i] {
                assert!(states[i] != State::Ready);
                after[i] = State::Ready;
                if let Kind::Part { app } = table[i].kind {
                    assert!(set[app] || states[app] == State::Ready);
                    behind_after[i] = true;
                }
            }
        }
        deliver(&table, &mut after, &behind_after);
        let again = bump_set(&table, &after, None);
        for i in 0..N {
            assert!(!again[i]);
        }
        let Ok(order) = publish_order(&table, &after, None) else {
            panic!("publish refused a plan that bump had settled");
        };
        let mut ready = 0;
        for i in 0..N {
            if after[i] == State::Ready {
                ready += 1;
            }
        }
        assert_eq!(order.len, ready);
    }

    #[kani::proof]
    #[kani::unwind(12)]
    fn a_named_bump_brings_the_application_of_each_part() {
        let table = any_table();
        let (states, _) = any_plan(&table);
        let named: [bool; N] = kani::any();
        let set = bump_set(&table, &states, Some(&named));
        for i in 0..N {
            if named[i] && states[i] != State::Ready {
                assert!(set[i]);
            }
            if set[i] {
                assert!(states[i] != State::Ready);
                if let Kind::Part { app } = table[i].kind {
                    assert!(set[app] || states[app] == State::Ready);
                }
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(12)]
    fn publish_releases_only_what_is_ready_with_its_carrier_and_parts_first() {
        let table = any_table();
        let states: [State; N] = kani::any();
        let named: Option<[bool; N]> = kani::any();
        let Ok(order) = publish_order(&table, &states, named.as_ref()) else {
            return;
        };
        assert!(order.len <= N);
        let mut seen = [false; N];
        let mut wave = 0;
        for position in 0..order.len {
            let i = order.items[position];
            assert!(!seen[i]);
            seen[i] = true;
            assert!(states[i] == State::Ready);
            if let Kind::Part { app } = table[i].kind {
                assert!(states[app] == State::Ready);
            }
            assert!(rank(table[i].kind) >= wave);
            wave = rank(table[i].kind);
        }
        for i in 0..N {
            let wanted = match &named {
                Some(named) => named[i],
                None => states[i] == State::Ready,
            };
            assert_eq!(seen[i], wanted);
            if named.is_none() && seen[i] {
                if let Kind::Part { app } = table[i].kind {
                    assert!(seen[app]);
                }
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(7)]
    #[kani::solver(kissat)]
    fn the_desktop_floor_covers_every_later_release_and_is_the_oldest_that_does() {
        let want: [u64; 3] = kani::any();
        let all: [Option<[u64; 3]>; DESKTOPS] = kani::any();
        let len: usize = kani::any();
        kani::assume(len <= DESKTOPS);
        let speaks = &all[..len];
        let covers = |i: usize| speaks[i].is_some_and(|version| version >= want);
        match oldest_covering(want, speaks) {
            Some(floor) => {
                assert!(floor < len);
                let later: usize = kani::any();
                kani::assume(later >= floor && later < len);
                assert!(covers(later));
                assert!(floor == 0 || !covers(floor - 1));
            }
            None => {
                assert!(len == 0 || !covers(len - 1));
            }
        }
    }

    #[kani::proof]
    fn successor_matches_checked_ordered_increment_for_all_u64_pairs() {
        let value: u64 = kani::any();
        let maximum: u64 = kani::any();
        let expected = if value < maximum {
            Some(value + 1)
        } else {
            None
        };
        assert_eq!(successor(value, maximum), expected);
    }
}
