---
name: pure-release-planning
description: Plan version bumps and publish order with the pure-release crate. Use when calling or changing code that uses pure_release (valid, state, deliver, bump_set, publish_order, successor, oldest_covering), or when adding a component to a release table.
---

`pure-release` decides what to bump and in which order to publish. It is `no_std`, has no dependencies, and does no I/O: the caller reads tags, versions and diffs, and passes the facts in.

# The table

One `Link` per component; the array index is the component's identity in every argument and result.

- `Kind::Part { app }`: reaches users only through the application at index `app` (a net core, a bootloader).
- `Kind::App`: carries parts.
- `Kind::Other`: released on its own.
- `manual: true`: bumped only when named.

# Call order

1. `valid(&table)` once, and refuse to continue on `false`. Every other table function assumes a valid table; with an invalid one a part's `app` index can be out of range.
2. `state(ahead, changed)` per component. `ahead` is `source.cmp(&newest_tag)`, or `None` for a component never released. `Err(Regressed)` means the source is below a released version: stop, do not coerce it to a state.
3. `deliver(&table, &mut states, &behind)` makes an application release when one of its parts is on its way out or its newest entry carries an older part (`behind[i]`). It rewrites `states`; use the rewritten array from here on. The result names the part that forced each application.
4. `bump_set(&table, &states, named)` gives the components to raise. Raise a counter with `successor(value, maximum)`; `None` means the counter is exhausted, never wrap it.
5. `publish_order(&table, &states, named)` gives `Order::as_slice()`: table indices, parts first. Handle both refusals: `Refusal::NotReady(index)` and `Refusal::NoCarrier { part, app }`.
6. `oldest_covering(want, speaks)` finds the oldest release from which every later one speaks at least `want`. `speaks` is oldest first; `None` marks a release without the wire constant.

`named` is `None` for "everything that qualifies", or `Some(&[bool; N])` selecting components by index.

# What the proofs cover

Verus verifies all seven release properties for arbitrary table sizes and compatibility-history lengths. Run `tools/verify-verus.sh` with the pinned verifier on `PATH`; its strict flags reject unproved assumptions and skipped executable bodies. Reuse `vstd` for general mathematical lemmas; keep release-specific facts in the checked helper module.

Kani independently checks every valid table and combination of states at `COMPONENT_COUNT` (11) components, and `oldest_covering` for histories of zero through five releases. Both verifiers cover arbitrary `u64` version triples. No runtime or Cargo dependencies are added by the Verus annotations.

The proofs say nothing about hardware behaviour, about how changes and dependencies are discovered, or about whether a change needs a major version bump.
