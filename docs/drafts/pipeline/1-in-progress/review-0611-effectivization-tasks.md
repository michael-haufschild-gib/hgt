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
| A17 | partial: star horizons done (`HodgeTheoryWithoutVarieties/TheDepthLawIsEffective`); Künneth jets closed as equivalence (`ArithmeticHarmonicAnalysis/SameOrderJetRecoveryIsHomogeneousLogIndependence`); gcd strata have the exact identity `completeWeilEnergy_gcd_stratification`; primitive depth-law constants not explicit, not started | |
| A18 | done | `SquareRootThreshold/EffectiveHorizons/HausdorffQuadraticRegion.lean`: `scaledHausdorffMomentDifference_nonneg_of_quadratic_le`, every entry with `r ≥ C₀(k+1)²` is nonnegative for the closed-form `hausdorffQuadraticConstant`; input `ZeroConfigurationGeometry/EffectiveHeights/TwoSidedZetaCount.lean`: `N(a,b)` two-sided with absolute constants (`le_xiZeroCount_window`, `xiZeroCount_window_le`, `xiZeroCount_le_explicit`) |
| A14 | done | `CompletedArithmeticForms/ThePrefixSchurCostIsThePrefixResidual.lean`: `S(tail z) = zᵀWz − rᵀA⁻¹r`, `r=(Wz)|_{[1,M]}`, so the debit is the prefix residual; `exists_plateauPrefixSchur_floor_on_conductor_block`: Schur complement keeps the conductor floor on fixed blocks. The crude `20‖By‖²` is false there (`By ∋ Ap`, size `log N`). Fixed-cell first-prime, coarse, polar costs: `ArithmeticIndexDescent/FixedCoarseCellsControlTheEntireWeilIndex.lean`, index `≤ R+A` on the literal full form |
| A13 | done | `CriticalArithmeticCorrelationTheory/ReceivingCharges/LiteralChannelScaleDomination.lean`: cutoffs `A=MQ²⌈log N⌉`, `J=⌊N/(ceQ²)⌋` dominate all five costs on `ceMQ⁵⌈log N⌉≤N`, `‖U‖²≤K(BVW)²(s²(1+S)²+(sA_P)²/R²)`; whole band `exists_literal_upward_full_band_bound`; coherent law `‖U‖≤KBVW|t|(1/√log Q+ω_Q(M)/log Q)`; literal centered charge `≤KBW|t|/√log Q` at every admissible horizon |
| A12 | not started | |
| A11 | partial: `θ<1/4` done (`EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans`); past `1/4` not started | |
| A10 | not started | |

## Rule

Explicit means a closed expression. A theorem `∃ C, RHVerifiedThrough (C …) → X` with `X` implied by RH is classically
trivial, so heights carry explicit values.
