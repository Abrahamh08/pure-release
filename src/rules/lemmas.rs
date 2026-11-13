//! Proof steps the executable rules call. Verus checks every one, so nothing
//! here adds to what has to be trusted.

use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_contains_after_push;
use vstd::set_lib::{lemma_int_range, lemma_len_subset, set_int_range};

use super::spec::{
    asked, before, carries_asked_below, forces, forcing_below, in_release_order, is_part_of,
    rank_of, valid_table,
};
use super::{Link, State};

verus! {

pub proof fn lemma_forcing_step(
    table: Seq<Link>,
    states: Seq<State>,
    behind: Seq<bool>,
    app: int,
    bound: int,
)
    ensures
        forcing_below(table, states, behind, app, bound + 1) <==> forcing_below(
            table,
            states,
            behind,
            app,
            bound,
        ) || forces(table, states, behind, bound, app),
{
    if forcing_below(table, states, behind, app, bound + 1) {
        let part = choose|part: int| part < bound + 1 && forces(table, states, behind, part, app);
        if part < bound {
            assert(forcing_below(table, states, behind, app, bound));
        }
    }
    if forcing_below(table, states, behind, app, bound) {
        let part = choose|part: int| part < bound && forces(table, states, behind, part, app);
        assert(part < bound + 1 && forces(table, states, behind, part, app));
    }
    if forces(table, states, behind, bound, app) {
        assert(forcing_below(table, states, behind, app, bound + 1));
    }
}

pub proof fn lemma_carrying_step(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    app: int,
    bound: int,
)
    requires
        bound >= 0,
    ensures
        carries_asked_below(table, states, named, app, bound + 1) <==> carries_asked_below(
            table,
            states,
            named,
            app,
            bound,
        ) || (is_part_of(table, bound, app) && asked(table, states, named, bound)),
{
    if carries_asked_below(table, states, named, app, bound + 1) {
        let part = choose|part: int|
            0 <= part < bound + 1 && is_part_of(table, part, app) && asked(table, states, named, part);
        if part < bound {
            assert(carries_asked_below(table, states, named, app, bound));
        }
    }
    if carries_asked_below(table, states, named, app, bound) {
        let part = choose|part: int|
            0 <= part < bound && is_part_of(table, part, app) && asked(table, states, named, part);
        assert(0 <= part < bound + 1 && is_part_of(table, part, app));
    }
    if is_part_of(table, bound, app) && asked(table, states, named, bound) {
        assert(carries_asked_below(table, states, named, app, bound + 1));
    }
}

/// Only applications carry parts in a valid table.
pub proof fn lemma_parts_carry_nothing(
    table: Seq<Link>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
    bound: int,
)
    requires
        valid_table(table),
        bound <= table.len(),
        !(table[i].kind is App),
    ensures
        !carries_asked_below(table, states, named, i, bound),
{
    if carries_asked_below(table, states, named, i, bound) {
        let part = choose|part: int|
            0 <= part < bound && is_part_of(table, part, i) && asked(table, states, named, part);
        assert(table[part].kind is Part);
    }
}


/// Appending the next component of the current wave keeps the release order,
/// and there is still room for it.
pub proof fn lemma_release_next(table: Seq<Link>, released: Seq<usize>, next: usize, wave: int)
    requires
        next < table.len(),
        rank_of(table[next as int].kind) == wave,
        in_release_order(table, released),
        forall|p: int| 0 <= p < released.len() ==> #[trigger] released[p] < table.len(),
        forall|p: int|
            0 <= p < released.len() ==> {
                let at = #[trigger] released[p] as int;
                rank_of(table[at].kind) < wave || (rank_of(table[at].kind) == wave && at < next)
            },
    ensures
        released.len() < table.len(),
        in_release_order(table, released.push(next)),
        forall|value: usize|
            #[trigger] released.push(next).contains(value) <==> released.contains(value) || value == next,
{
    let grown = released.push(next);
    assert forall|p: int, q: int| 0 <= p < q < grown.len() implies before(
        table,
        #[trigger] grown[p] as int,
        #[trigger] grown[q] as int,
    ) by {
        if q < released.len() {
            assert(before(table, released[p] as int, released[q] as int));
        } else {
            assert(grown[p] == released[p]);
        }
    }
    let values = grown.map_values(|value: usize| value as int);
    assert forall|a: int, b: int| 0 <= a < values.len() && 0 <= b < values.len() && a != b implies values[a]
        != values[b] by {
        if a < b {
            assert(before(table, grown[a] as int, grown[b] as int));
        } else {
            assert(before(table, grown[b] as int, grown[a] as int));
        }
    }
    assert forall|k: int| 0 <= k < values.len() implies 0 <= #[trigger] values[k] < table.len() by {
        if k < released.len() {
            assert(grown[k] == released[k]);
        }
    }
    values.unique_seq_to_set();
    lemma_int_range(0, table.len() as int);
    let indices = set_int_range(0, table.len() as int);
    assert(values.to_set().subset_of(indices)) by {
        assert forall|value: int| values.to_set().contains(value) implies indices.contains(value) by {
            let k = choose|k: int| 0 <= k < values.len() && values[k] == value;
            assert(0 <= values[k] < table.len());
        }
    }
    lemma_len_subset(values.to_set(), indices);
    broadcast use lemma_seq_contains_after_push;
}

}
