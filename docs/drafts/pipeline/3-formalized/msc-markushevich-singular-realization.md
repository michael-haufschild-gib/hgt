# MSC Markushevich singular realization

- **ID:** MSC-MBASIS-SINGULAR
- **Stage:** 3-formalized
- **Result:** For `1/2 < Re ρ`, exact physical MSC source/overlap columns admit an explicit positive Hilbert realization whose normalized modes and explicit biorthogonal dual are both complete. For `Re ρ ≤ 1`, every Bessel bound fails on a finite packet.
- **Route kill:** `source M-basis rigidity ⇒ stability` is false. Positivity and Markushevich completeness cannot force `Re ρ > 1`; quantitative Bessel/frame stability remains necessary.
- **Construction:** Dyadic squarefree blocks, phase-twisted finite regular-simplex dual bases, and an orthogonal residual carrier. Block source/overlap energy is summable exactly on the required half-strip.
- **Lean:** `HTGeometry/FiniteMarkushevichSimplexBlock.lean`; `RHTower/HedenmalmGammaSewnSquarefreeFisherMarkushevichSingularRealization.lean`; endpoint `strictRightXiZero_mscMarkushevichSingularRouteKill`.
- **Audit:** Targeted `lake build` passed. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Corpus lint has unrelated pre-existing umbrella reachability failures; both new modules are wired.
- **Novelty:** Corpus and primary-literature audit through 2026-08 found no prescribed two-column MSC Markushevich realization or this `ℓ²\ℓ¹` threshold construction.
