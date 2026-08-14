Formalized exact diagonal removal for selector-resolved recurrence.

Module:
formal/GaloisForLFunctions/HTGeometry/StaticShortcutCrossRecurrenceCapacityLaw.lean
Umbrella: formal/GaloisForLFunctions/HTGeometry.lean

Key laws:
- selector recurrence = diagonal self-memory + distinct-time same-channel cross recurrence.
- eta^2 W^2 - B K D_self <= B K R_cross.
- Under norm^2 <= D and off-diagonal inner <= mu:
  (eta^2 - B mu) W^2 <= B K (D-mu) sum w_j^2.
- Unit-weight cardinality corollary formalized.

Key declarations:
selectorRecurrenceEnergy_eq_diagonal_add_cross
selectorLoadEnergy_eq_diagonal_add_cross
selectorCapacity_forces_crossRecurrence
selectorCoherenceGap_mul_load_le_diagonal
selectorMass_sq_le_capacity_mul_diagonal_of_coherence
selectorOccupiedChannels_gt_of_coherenceBudget_lt
selectorCard_sq_le_capacity_mul_card_of_coherence

Verification:
- lake env lean module passed.
- leaf-only lake build module passed.
- axioms only propext, Classical.choice, Quot.sound.
- no full build.
- scratch files removed, no stale task Lean.

Paper cards:
docs/drafts/pipeline/2-fully-proven/return-excised-cross-recurrence-capacity-law.md
docs/drafts/pipeline/3-formalized/return-excised-cross-recurrence-capacity-law.md

Hostile boundary:
This is a sharp deterministic frontier reduction, not Brown onset. Fresh-channel diagonal contamination is retired. Uniform pairwise coherence is only a sufficient condition; no ordinary local-H ensemble bound is proved. Since circuit-channel capacity is exponential in depth, deterministic history counting alone yields at best logarithmic depth. Remaining core is quenched growing-replica/direct incidence-action decay for one ordinary static local H, uniform over complete approximate shallow-circuit selectors, then same-event plateau and first low-complexity recurrence.