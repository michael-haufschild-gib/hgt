# Noninvertible events require a complementary record

- **ID:** `noninvertible-event-complementary-record-boundary`
- **Stage:** 3-formalized
- **Type:** EXACT LINEAR-ALGEBRA NO-GO / MINIMAL-RECORD CLASSIFICATION / PHYSICS BRIDGE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../../2-fully-proven/not_new_scientific_knowledge/noninvertible-event-complementary-record-boundary.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/EventComplementaryRecord.lean`

## Formal theorem

For a linear event `T : V → W`:

1. `ker T ≤ ker (F ∘ T)` for every later linear report `F`;
2. if the combined event and record `(T,R) : V → W × E` is injective, then
   `R|ker(T)` is injective and `finrank(ker T) ≤ finrank(E)`;
3. if `finrank(V) = finrank(W)` and `E = coker(T)`, that restricted record is bijective;
4. for a ten-to-ten event, the same bijection applies, while the imported rank-six theorem
   identifies both kernel and cokernel dimensions as four; and
5. a linear record invariant under one nontrivial scalar rescaling is zero.

The combined result proves both necessity and noncanonicity: a faithful noninvertible event needs
a record large enough to retain its kernel, but the bare event map cannot naturally choose a
nonzero kernel--cokernel pairing.

## Lean declarations

```text
eventRecordOnKernel
eventKernel_le_postReportKernel
eventRecordOnKernel_injective
eventRecord_finrank_lower_bound
eventKernel_finrank_eq_coker_of_equal_finrank
eventRecordOnKernel_bijective_of_combined_injective
rankSixEvent_recordOnKernel_bijective
linearRecord_eq_zero_of_scaling_invariant
```

## Verification

- scratch proof against pinned toolchain: passed;
- direct `lake env lean GaloisForLFunctions/HTGeometry/EventComplementaryRecord.lean`: passed
  without warnings;
- final `lake build GaloisForLFunctions.HTGeometry.EventComplementaryRecord`: passed
  (`2946/2946`);
- `scripts/formal_tools.py lint`: passed;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- no stale Lean or Lake process remained.

## Novelty and physics boundary

`[NOT NEW MATHEMATICS]` These are rank--nullity, quotient dimension, observability, and scalar
naturality consequences.  Stinespring dilation, complementary channels, no-hiding, and
information--disturbance results occupy the quantum analogue.

Lean does **not** prove that the record is spacetime, that its dimension is Lorentzian dimension,
or that its connection yields gravity and gauge forces.  Those claims remain the open
source-natural complementary-record conjecture.

## Research consequence

The former universal clause “every real distinction has a future consequence” is either
definitional after operational quotienting or false for a noninjective event.  The exact survivor
is stronger and narrower:

> A noninvertible physical event can conserve source distinctions only through an additional
> complementary record; at the rank-six ten-to-ten boundary, every minimal cokernel-valued record
> pairs four erased directions with four created directions.

Whether physical law identifies this forced record with newly created spacetime is now a sharply
isolated scientific question.

## Log

- 2026-07-29 — dependency-closed paper theorem promoted to unconditional Lean.
- 2026-07-29 — module build, formal lint, and standard-foundation axiom audit passed.
