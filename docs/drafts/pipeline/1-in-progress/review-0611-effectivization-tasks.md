# Review-0611 §2.1 effectivization tasks (A10–A18)

- **ID:** review-0611-effectivization
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), one per task
- **Source:** [Obstacles summary §2.1](../../../reports/review-0611/obstacles-summary.md)
- **Statement:** Each task A10–A18 gets a complete unconditional Lean theorem, easiest first.

## Status

| Task | Status | Lean |
|---|---|---|
| A15 | done | `ZeroConfigurationGeometry/NegativeTests/SharpLocationHeight.lean`: `log(T₀(λ,c)/2π) ≤ max(4/(λ−1), 7Ω log(792Ω²/(λ−1)))`, `Ω=2.2·10¹⁷(c+51395)`, `1<λ≤2` |
| A16 | done | Interferometer `3-formalized/two-bump-interferometer-retains-complex-amplitudes.md`. Crystal `3-formalized/cut-crystal-hides-fixed-depth-at-logarithmic-aperture.md`, `WindowVisibilityLaw/TheCutCrystalHidesFixedDepth.lean`. Constants: `WindowVisibilityLaw/TheUniversalVisibilityThreshold.lean`: `k·pairEnergy(δ,a) ≤ (K/2)ℓe^{2(2π/ℓ+σ)a}` for every sea with `K` zeros per cell `2π/ℓ`, so `e^{2δa} ≤ 4δ(E/k+a)+1`; `WindowVisibilityLaw/TheTwoLobeTestHasAbsoluteConstants.lean`: `M_S e^{2(δ−σ)a} ≤ 12000A₀log(|γ₀|+4·10⁸A₀log(|γ₀|+3)+6)`, replacing `2²⁶δ(2a+2π)e^{2π}`; `SquareRootThreshold/ASharperClusterDetectorConstant.lean`: detector `480000` to `1200`, `n ≤ 282 log(|γ|+3)` from height `110` |
| A17 | star horizons done (`HodgeTheoryWithoutVarieties/TheDepthLawIsEffective`); Künneth jets closed as equivalence (`ArithmeticHarmonicAnalysis/SameOrderJetRecoveryIsHomogeneousLogIndependence`); gcd strata open | |
| A18 | quadratic region done with non-explicit `C` (`3-formalized/hausdorff-quadratic-saddle-region.md`) | `SquareRootThreshold/EffectiveHorizons/HausdorffQuadraticRegion` |
| A14 | open | |
| A13 | open | |
| A12 | open | |
| A11 | ledger row stale: `θ<1/4` done (`EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans`); past `1/4` open | |
| A10 | open | |

## Rule

Explicit means a closed expression. A theorem `∃ C, RHVerifiedThrough (C …) → X` with `X` implied by RH is classically
trivial, so heights carry explicit values.
