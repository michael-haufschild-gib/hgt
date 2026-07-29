# Canonical event-slice weak-order collapse

- **ID:** `canonical-event-slice-weak-order-collapse`
- **Stage:** 3-formalized
- **Type:** ORDER-THEORETIC NO-GO / POSITIVE CLASSIFICATION / SPACETIME BRIDGE
- **Status:** `[LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../2-fully-proven/not_new_scientific_knowledge/canonical-event-slice-weak-order-collapse.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/CanonicalEventSlice.lean`

## Exact formal theorem

For every partially ordered type, define augmented incomparability by

```text
¬ x < y ∧ ¬ y < x.
```

`orderGreatestCausalSlices_iff_augmentedIncomparable_transitive` proves:

```text
there exists a greatest causal antichain through every event
  iff
augmented incomparability is transitive.
```

The order-theoretic definition of “greatest” is exact: the slice contains its event, is an
antichain, and contains every antichain through that event.

Additional exact declarations:

- `augmentedIncomparable_refl`
- `augmentedIncomparable_symm`
- `causalAntichain_pair_of_augmentedIncomparable`
- `IsGreatestCausalSliceAt.mem_iff`
- `IsGreatestCausalSliceAt.antichain_subset`
- `IsOrderGreatestCausalSliceAt.isGreatest`
- `greatestCausalSliceAt_unique`
- `canonicalCausalSlice_isGreatest`
- `greatestCausalSlices_iff_augmentedIncomparable_transitive`
- `canonicalCausalSlice_eq_iff`
- `lt_or_gt_of_not_augmentedIncomparable`

## Exact conclusion

If causal order alone assigns one greatest spatial antichain to every event, equality-or-
incomparability becomes an equivalence relation. Its classes are the canonical slices, and events
in distinct classes are strictly comparable. This is precisely the strict-weak-order collapse to
an ordinal stack of simultaneity layers.

No gravity, spacetime, causal-set continuum limit, Standard Model group, or physical
event--boundary identity is proved.

## Verification

Commands:

```text
lake env lean GaloisForLFunctions/HTGeometry/CanonicalEventSlice.lean
lake build GaloisForLFunctions.HTGeometry.CanonicalEventSlice
```

Both passed. Dedicated module build completed `429/429`.

The separate `#print axioms` audit reports:

```text
orderGreatestCausalSlices_iff_augmentedIncomparable_transitive
  [propext]

canonicalCausalSlice_eq_iff
  [propext, Quot.sound]

lt_or_gt_of_not_augmentedIncomparable
  [propext, Classical.choice, Quot.sound]
```

These are standard Lean/mathlib logical principles; there are no project axioms, `sorry`,
`admit`, `opaque`, or `unsafe` declarations.

## Scientific status

The theorem is established weak-order mathematics and is not new scientific knowledge. Its
research value is the exact no-go boundary it supplies to
`event-boundary-identity-spacetime-law.md`: relativistic event-created space cannot be the unique
maximal antichain determined by causal order alone.

## Gates

- [x] exact dependency-closed paper proof
- [x] exact unconditional Lean theorem
- [x] targeted direct Lean check
- [x] dedicated final module build
- [x] axiom audit
- [x] formal lint
- [x] priority and physical-scope correction

## Log

- 2026-07-29 — formalized the exact positive classification extracted from the causality-only
  canonical-slice no-go.
