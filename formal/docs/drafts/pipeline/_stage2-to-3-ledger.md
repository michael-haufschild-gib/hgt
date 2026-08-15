
## Promoted: resolution/time noncommutativity law (2026-08-15)

`resolution-time-noncommutativity-static-local-complexity-law` moved to `3-formalized`.  Every
statement of the card is closed unconditionally in Lean 4 with axiom set
`[propext, Classical.choice, Quot.sound]`.

New module: `HTGeometry/ResolutionTimeNoncommutativity.lean` — `(3)` the easy interval at positive
resolution, `(8)` positive layer distance, `(4)` the resolution threshold, `(5)` both iterated
limits as genuine `Tendsto` statements, and `(10)` the uniform window threshold from compactness.

The whole circuit layer came free from `HTGeometry/ExactPenaltyCircuitBellman.lean`: `wordAct`,
`reachSet` (`Z_s`), `layerDist`, `approxComplexity` (`C_ε`), `isCompact_reachSet`,
`lt_layerDist_of_lt_approxComplexity`, `layerDist_le_dist`.  **Any card about circuit layers,
approximate complexity, or Bellman certificates should start there.**

The parent conclusions `(7)` and `(9)` (exponential exact bound and local finiteness) enter as
explicit hypotheses, exactly as in the paper proof.

40 cards remain in `2-fully-proven` (top level).
