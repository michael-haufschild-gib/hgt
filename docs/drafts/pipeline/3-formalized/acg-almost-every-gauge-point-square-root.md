# Almost every gauge point cancels to the square root

- **ID:** acg-ae-square-root-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry README §9 topic 2; MC half-power receiver
- **Statement:** For every bounded source, Haar-almost every gauge twist has partial sums
  `O(√N log² N)`; for `μ` the half-power law holds a.e., fails at the Liouville twin, and holds at
  the gauge point `0` iff RH.

## Proof
Dyadic chaining: every `n < 2^{K+1}` is a sum of ≤ one block per level, so
`sup|S_n|² ≤ (K+1)W_K`, `E W_K = (K+1)Σ_{n≤2^{K+1}}|a_n|²` by orthonormality of twists. Markov at
level `2^{K+1}(K+1)³` gives probability `≤ 1/(K+1)²`; Borel–Cantelli. Twin: `μλ = μ²`, squarefree
density `≥ 1/50` on `(K,2K]`. Point `0`: Littlewood's criterion
(`RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis`).

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/AlmostEveryGaugePointCancelsToTheSquareRoot.lean`:
`sq_norm_orthoSum_le`, `integral_dyadicEnergy`, `ae_exists_norm_orthoSum_le`,
`ae_exists_norm_gaugePartialSum_le`, `ae_gaugeHalfPowerLaw`, `gaugeHalfPowerLaw_moebius_zero_iff`,
`not_gaugeHalfPowerLaw_moebius_liouville`, `moebius_gauge_trichotomy`. Axioms: propext,
Classical.choice, Quot.sound.

## Insight
The half-power law is a Haar-full property of the Möbius gauge orbit; RH says the actual source is
not in the null exceptional set, which contains the Liouville twin. Multiplicative data cannot
decide it (the twin shares them).
