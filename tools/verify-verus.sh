#!/bin/sh
set -eu

command -v verus >/dev/null 2>&1 || {
    printf '%s\n' 'error: verus not found on PATH' >&2
    exit 127
}

theorems=src/rules/theorems.rs
[ -f "$theorems" ] || {
    printf '%s\n' "error: missing $theorems" >&2
    exit 1
}
grep -Eq '^[[:space:]]*verus![[:space:]]*\{' "$theorems" || {
    printf '%s\n' "error: $theorems has no Verus module" >&2
    exit 1
}

for theorem in \
    a_changed_component_is_never_current_and_a_regression_is_refused \
    delivery_leaves_no_outgoing_part_without_a_releasing_application \
    one_bump_leaves_nothing_to_bump_and_publish_then_accepts_everything_ready \
    a_named_bump_brings_the_application_of_each_part \
    publish_releases_only_what_is_ready_with_its_carrier_and_parts_first \
    the_desktop_floor_covers_every_later_release_and_is_the_oldest_that_does \
    successor_matches_checked_ordered_increment_for_all_u64_pairs
do
    if ! grep -Eq "^[[:space:]]*(pub[[:space:]]+)?(proof[[:space:]]+)?fn[[:space:]]+$theorem([<(]|[[:space:]])" "$theorems"; then
        printf '%s\n' "error: missing executable theorem function: $theorem" >&2
        exit 1
    fi
done

exec verus --crate-type=lib src/lib.rs --no-external-by-default --no-cheating --triggers-mode silent
