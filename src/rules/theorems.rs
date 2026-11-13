use core::cmp::Ordering;
use vstd::prelude::*;

use super::spec::{
    asked, at_least_spec, before, bumped, carries_asked_below, chosen, covers, forced, forces,
    forcing_below, in_release_order, is_part_of, names, outgoing, releases, valid_table,
};
use super::{
    Kind, Link, State, bump_set, deliver, oldest_covering, publish_order, state, successor,
};

verus! {

fn a_changed_component_is_never_current_and_a_regression_is_refused(
    ahead: Option<Ordering>,
    changed: bool,
) {
    let result = state(ahead, changed);
    assert(result is Err <==> ahead == Some(Ordering::Less));
    match ahead {
        None => { assert(result == Ok::<State, super::Regressed>(State::Ready)); },
        Some(Ordering::Less) => { assert(result is Err); },
        Some(Ordering::Equal) => {
            assert(result == Ok::<State, super::Regressed>(if changed { State::NeedsBump } else { State::Current }));
        },
        Some(Ordering::Greater) => { assert(result == Ok::<State, super::Regressed>(State::Ready)); },
    }
    assert(changed ==> result != Ok::<State, super::Regressed>(State::Current));
    assert(ahead == Some(Ordering::Equal) && !changed ==> result == Ok::<State, super::Regressed>(State::Current));
    assert(ahead is None || ahead == Some(Ordering::Greater) ==> result == Ok::<State, super::Regressed>(State::Ready));
}

fn delivery_leaves_no_outgoing_part_without_a_releasing_application<const N: usize>(
    table: &[Link; N],
    initial: [State; N],
    behind: &[bool; N],
)
    requires valid_table(table@),
{
    let mut states = initial;
    let result = deliver(table, &mut states, behind);
    assert forall|i: int| 0 <= i < N implies
        states@[i] == initial@[i]
        || (initial@[i] is Current && states@[i] is NeedsBump && table@[i].kind is App) by {
        if forced(table@, initial@, behind@, i) {
            let part = choose|part: int| part < N && forces(table@, initial@, behind@, part, i);
            assert(table@[part].kind is Part);
        }
    }
    assert forall|i: int| 0 <= i < N implies
        (result@[i] is Some <==> initial@[i] is Current && states@[i] is NeedsBump) by {}
    assert forall|part: int, app: int|
        0 <= part < N && 0 <= app < N
            && is_part_of(table@, part, app)
            && outgoing(table@, states@, behind@, part)
        implies !(states@[app] is Current) by {
        assert(table@[part].kind is Part);
        assert(states@[part] == initial@[part]);
        assert(outgoing(table@, initial@, behind@, part));
        assert(forces(table@, initial@, behind@, part, app));
        assert(forcing_below(table@, initial@, behind@, app, N as int));
    }
    let mut again = states;
    deliver(table, &mut again, behind);
    assert forall|app: int| 0 <= app < N implies !forced(table@, states@, behind@, app) by {
        if forced(table@, states@, behind@, app) {
            let part = choose|part: int| part < N && forces(table@, states@, behind@, part, app);
            assert(table@[part].kind is Part);
        }
    }
    assert(again@ == states@);
}

#[verifier::loop_isolation(false)]
fn one_bump_leaves_nothing_to_bump_and_publish_then_accepts_everything_ready<const N: usize>(
    table: &[Link; N],
    initial: [State; N],
    behind: [bool; N],
)
    requires valid_table(table@),
{
    let mut states = initial;
    deliver(table, &mut states, &behind);
    assert forall|part: int, app: int|
        0 <= part < N && 0 <= app < N && forces(table@, states@, behind@, part, app)
        implies !(states@[app] is Current) by {
        assert(table@[part].kind is Part);
        assert(states@[part] == initial@[part]);
        assert(forces(table@, initial@, behind@, part, app));
        assert(forcing_below(table@, initial@, behind@, app, N as int));
    }
    let set = bump_set(table, &states, None);
    let mut after = states;
    let mut behind_after = behind;
    for i in 0..N
        invariant
            forall|j: int| 0 <= j < N ==> after@[j] == (
                if j < i && set@[j] { State::Ready } else { states@[j] }),
            forall|j: int| 0 <= j < N ==> behind_after@[j] == (
                behind@[j] || (j < i && set@[j] && table@[j].kind is Part)),
    {
        assert(states@[i as int] is NeedsBump && !table@[i as int].manual ==> set@[i as int]);
        if set[i] {
            assert(!(states@[i as int] is Ready));
            after[i] = State::Ready;
            if let Kind::Part { app } = table[i].kind {
                assert(set@[app as int] || states@[app as int] is Ready) by {
                    super::lemmas::lemma_parts_carry_nothing(table@, states@, None, i as int, N as int);
                    assert(asked(table@, states@, None, i as int));
                    assert(is_part_of(table@, i as int, app as int));
                    assert(carries_asked_below(table@, states@, None, app as int, N as int));
                }
                behind_after[i] = true;
            }
        }
    }
    assert forall|part: int, app: int|
        0 <= part < N && 0 <= app < N && is_part_of(table@, part, app)
            && set@[part]
        implies after@[app] is Ready by {
        super::lemmas::lemma_parts_carry_nothing(table@, states@, None, part, N as int);
        assert(asked(table@, states@, None, part));
        assert(carries_asked_below(table@, states@, None, app, N as int));
    }
    assert forall|app: int| 0 <= app < N
        implies !forced(table@, after@, behind_after@, app) by {
        if forced(table@, after@, behind_after@, app) {
            let part = choose|part: int| part < N && forces(table@, after@, behind_after@, part, app);
            assert(is_part_of(table@, part, app));
            assert(table@[part].kind is Part);
            assert(!set@[part]);
            assert(forces(table@, states@, behind@, part, app));
            assert(!(states@[app] is Current));
        }
    }
    let ghost before_delivery = after@;
    deliver(table, &mut after, &behind_after);
    assert(after@ == before_delivery);
    assert forall|i: int| 0 <= i < N implies !asked(table@, after@, None, i) by {
        assert(set@[i] == bumped(table@, states@, None, i));
    }
    let again = bump_set(table, &after, None);
    assert forall|i: int| 0 <= i < N implies !again@[i] by {
        if carries_asked_below(table@, after@, None, i, N as int) {
            let part = choose|part: int| 0 <= part < N
                && is_part_of(table@, part, i) && asked(table@, after@, None, part);
        }
    }
    assert forall|part: int| 0 <= part < N
        implies !super::spec::no_carrier(table@, after@, None, part) by {
        if super::spec::no_carrier(table@, after@, None, part) {
            let app = match table@[part].kind { Kind::Part { app } => app as int, _ => 0 };
            assert(forces(table@, states@, behind@, part, app) || set@[part]);
            assert(table@[part].kind is Part);
            assert(table@[app].kind is App && !table@[app].manual);
            assert(set@[app] == bumped(table@, states@, None, app));
            assert(is_part_of(table@, part, app));
            if set@[part] {
                assert(after@[app] is Ready);
            } else {
                assert(forces(table@, states@, behind@, part, app));
                assert(!(states@[app] is Current));
            }
            assert(0 <= app < N);
            assert(after@[app] == (if set@[app] { State::Ready } else { states@[app] }));
            assert(states@[app] is NeedsBump ==> set@[app]);
            assert(after@[app] is Ready);
        }
    }
    let published = publish_order(table, &after, None);
    assert(published is Ok);
    if let Ok(order) = published {
        let indices = order.as_slice();
        assert forall|i: int| 0 <= i < N implies
            (indices@.contains(i as usize) <==> after@[i] is Ready) by {
            assert(chosen(after@, None, i) == (after@[i] is Ready));
        }
        let ghost ready = Set::<int>::range(0, N as int).filter(|i: int| after@[i] is Ready);
        let ghost released = indices@.map_values(|i: usize| i as int);
        assert(released.no_duplicates()) by {
            assert forall|a: int, b: int|
                0 <= a < released.len() && 0 <= b < released.len() && a != b
                implies released[a] != released[b] by {
                if a < b {
                    assert(before(table@, indices@[a] as int, indices@[b] as int));
                } else {
                    assert(before(table@, indices@[b] as int, indices@[a] as int));
                }
            }
        }
        proof { released.unique_seq_to_set(); }
        assert(released.to_set() =~= ready) by {
            assert forall|value: int| released.to_set().contains(value)
                implies ready.contains(value) by {
                let p = choose|p: int| 0 <= p < released.len() && released[p] == value;
                assert(indices@[p] < N);
                assert(indices@.contains(value as usize));
            }
            assert forall|value: int| ready.contains(value)
                implies released.to_set().contains(value) by {
                assert(0 <= value < N && after@[value] is Ready);
                assert(indices@.contains(value as usize));
                let p = choose|p: int| 0 <= p < indices@.len() && indices@[p] == value;
                assert(released[p] == value);
            }
        }
        assert(indices@.len() == ready.len());
    }
}

fn a_named_bump_brings_the_application_of_each_part<const N: usize>(
    table: &[Link; N],
    initial: [State; N],
    behind: &[bool; N],
    named: &[bool; N],
)
    requires valid_table(table@),
{
    let mut states = initial;
    deliver(table, &mut states, behind);
    let set = bump_set(table, &states, Some(named));
    assert forall|i: int| 0 <= i < N && named@[i] && !(states@[i] is Ready)
        implies set@[i] by {}
    assert forall|part: int, app: int|
        0 <= part < N && 0 <= app < N && set@[part] && is_part_of(table@, part, app)
        implies set@[app] || states@[app] is Ready by {
        assert(table@[part].kind is Part);
        if carries_asked_below(table@, states@, Some(named@), part, N as int) {
            let nested = choose|nested: int| 0 <= nested < N
                && is_part_of(table@, nested, part) && asked(table@, states@, Some(named@), nested);
            assert(table@[part].kind is App);
        }
        assert(carries_asked_below(table@, states@, Some(named@), app, N as int));
    }
    assert forall|i: int| 0 <= i < N && set@[i] implies !(states@[i] is Ready) by {}
}

fn publish_releases_only_what_is_ready_with_its_carrier_and_parts_first<const N: usize>(
    table: &[Link; N],
    states: &[State; N],
    named: Option<&[bool; N]>,
)
    requires valid_table(table@),
{
    let published = publish_order(table, states, named);
    if let Ok(order) = published {
        let indices = order.as_slice();
        assert(in_release_order(table@, indices@));
        assert(indices@.no_duplicates()) by {
            assert forall|p: int, q: int|
                0 <= p < indices@.len() && 0 <= q < indices@.len() && p != q
                implies indices@[p] != indices@[q] by {
                if p < q {
                    assert(before(table@, indices@[p] as int, indices@[q] as int));
                } else {
                    assert(before(table@, indices@[q] as int, indices@[p] as int));
                }
            }
        }
        assert forall|i: int| 0 <= i < N implies
            (indices@.contains(i as usize) <==> chosen(states@, names(named), i)) by {}
        assert forall|i: int| 0 <= i < N && indices@.contains(i as usize)
            implies states@[i] is Ready by {
            assert(chosen(states@, names(named), i));
            assert(!super::spec::not_ready(states@, names(named), i));
        }
        assert forall|part: int, app: int|
            0 <= part < N && 0 <= app < N
                && indices@.contains(part as usize) && is_part_of(table@, part, app)
            implies states@[app] is Ready
                && (named is None ==> indices@.contains(app as usize)) by {
            assert(chosen(states@, names(named), part));
            assert(!super::spec::no_carrier(table@, states@, names(named), part));
            if named is None {
                assert(chosen(states@, None, app));
            }
        }
    }
}

fn the_desktop_floor_covers_every_later_release_and_is_the_oldest_that_does(
    want: [u64; 3],
    speaks: &[Option<[u64; 3]>],
) {
    let result = oldest_covering(want, speaks);
    match result {
        Some(floor) => {
            assert(floor < speaks.len());
            assert forall|later: int| floor <= later < speaks@.len()
                implies covers(want, speaks@, later) by {}
            assert(floor == 0 || !covers(want, speaks@, floor - 1));
        },
        None => { assert(speaks@.len() == 0 || !covers(want, speaks@, speaks@.len() - 1)); },
    }
}

fn successor_matches_checked_ordered_increment_for_all_u64_pairs(value: u64, maximum: u64) {
    let result = successor(value, maximum);
    if value < maximum {
        assert(result == Some((value + 1) as u64));
    } else {
        assert(result is None);
    }
}

}
