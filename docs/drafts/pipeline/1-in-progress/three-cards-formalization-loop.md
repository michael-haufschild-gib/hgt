# Three-card formalization loop (Metzler, cutoff gap, Hawking–Page)

- **ID:** three-cards-formalization-loop-2011
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Formalize unconditionally every proven theorem of the three cards below and move them to 3-formalized.

## Cards
1. 2-fully-proven/trans-metzler-weil-positivity.md — programme `TransMetzlerWeilPositivity`.
2. 2-fully-proven/arithmetic-counting-positive-density-exact-cutoff-gap.md — `ArithmeticCountingPositivity/PositiveDensityTransfersTheExactCutoffGap.lean`.
3. 2-fully-proven/arithmetic-hawking-page-phase-and-ads-modular-horizon-resolution.md — `CausalReflection/ArithmeticHawkingPagePhaseStructure.lean`, `BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean`.

## Gaps (card claim without a Lean theorem)
- [x] G1 (card 1, Part IV.1) — `TransMetzlerWeilPositivity/FejerBlocksGiveTheSharpCenterFloor.lean`: exact Fejér SOS identity, Toeplitz floor `-3/2`, public Hilbert floor `-1/2`, center-kernel floor `-Σ n x_n²`.
- [x] G2 (card 1, Q1.3) — `FiniteOffLineSupportPaysABoundedCodimension.lean`: finite off-line support ⇒ `weilQuad ≥ 0` on a coefficient subspace of codimension `≤ #rightZeros`.
- [x] G3 (card 1, Q1.4) — `AComplexZeroWeighsLinearlyInTheOverlap.lean`: linear-in-`c` lower bound `|Wsummand| ≥ κ c ‖x‖² ∫g²` at a complex off-line zero, `x_n = cos(γ₀ log n)`.
- [x] G4 (card 3, step 4) — `uniform_neutral_control`, `locallyLipschitzOn_deriv_confiningHalfLineGroundEnergy` (ConfiningGlobalTransverseGapAndResponse); bundle + occupation law in `CausalReflection/TheConfiningSaddleHasAnOccupationLawAndPositiveSusceptibility.lean`: `μ` is `C^{1,1}_loc` on `(0,∞)` (locally Lipschitz derivative); requires a locally uniform transverse gap.
- [x] G5 (card 1, Part I.1) — `TheExplicitPlateauHasAConductorOneMargin.lean`: Robin margin `≥ 477001/250000`, `E(1) > 68/1000`, `E(m) > E(1)` for `m ≥ 2`.
- [x] G6 (card 1, Part III.1) — `TheSteklovProfileHasUnitL1DerivativeProducts.lean`: `∫|φ_DC^{(q)}| ≤ ∏_{j<q} a_j⁻¹ ≤ 6·16^q W_q` (L¹ Steklov contraction).
- [x] G7 (card 1, Part III.1) — same module: `steklovDCProfile ≥ 0`.
- [x] Wiring: `PrimeTwoDeformedApertureLogTwoTest` and `ArithmeticHawkingPagePhaseStructure` into their umbrellas; direct import of the cutoff-gap module.
- [ ] Final audit: all card modules compile clean with standard axioms (ExplicitPlateauParameters, TransMetzlerDecomposition, TransMetzlerPositivity, LiouvilleTwinSelectivity, SuperGevreyCriticalGrowth, ZeroSideStratum, the five new TMWP modules, PositiveDensityTransfersTheExactCutoffGap, ConfiningMinimizerOuterAndCyclic, ConfiningGlobalTransverseGapAndResponse, ConfiningSourceEndpointSelection, ConfiningHalfLineGroundEnergyCurvature, ArithmeticHawkingPagePhaseStructure, the new occupation/susceptibility module). Remaining: `PrimeTwoDeformedApertureLogTwoTest` check, blocked on a chain of missing WindowTowerOfSpecZ oleans (being built one by one). one foreground `lake --old env lean` per module + headline `#print axioms`.

## Covered (claim → Lean)
See each card's Lean section once moved.

## Status
PAUSED by user 2026-11-20 after finishing the running Lean work. Remaining steps: PrimeTwo check (if not finished), then card Lean sections + move of the three cards to 3-formalized.
