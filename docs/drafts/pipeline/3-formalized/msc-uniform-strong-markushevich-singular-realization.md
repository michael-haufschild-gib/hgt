# MSC uniform strong Markushevich singular realization

- **ID:** MSC-STRONG-MBASIS-SINGULAR
- **Stage:** 3-formalized
- **Result:** For `1/2 < Re ρ`, literal physical MSC columns admit an explicit strong Markushevich pair: every primal/dual mixed system is complete, primal norms equal one, and dual squared norms are at most two. For `Re ρ ≤ 1`, every Bessel bound still fails.
- **Route kill:** `source hereditary completeness + uniform minimality ⇒ Bessel/frame stability` is false; neither property can force `Re ρ > 1` or exclude a strict-right Xi zero.
- **Mechanism:** On each dyadic squarefree block, every mixed simplex family has positive total mean coefficient, forcing both mean and centered orthogonal components to vanish. Orthogonal block lifting handles arbitrary global selectors.
- **Lean:** `HTGeometry/StrongMarkushevichSystem.lean`; `HTGeometry/FiniteMarkushevichSimplexBlock.lean`; `RHTower/Hedenmalm/HedenmalmGammaSewnSquarefreeFisherUniformStrongMarkushevichSingularRealization.lean`; endpoint `strictRightXiZero_mscUniformStrongMarkushevichSingularRouteKill`.
- **Novelty:** General strong M-bases are known, but corpus and primary-literature audit through 2026-08 found no prescribed literal two-column MSC realization with this half-strip/non-Bessel threshold.
- **Audit:** Targeted build passed. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Corpus lint has unrelated pre-existing umbrella reachability failures; all new modules are wired.
