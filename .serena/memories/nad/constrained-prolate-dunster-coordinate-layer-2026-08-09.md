# Dunster coordinate + weight + endpoint expansion layer (2026-08-09)

Card: `docs/drafts/pipeline/2-fully-proven/nad/constrained-prolate-continuous-polar-charge-law.md`.
All wired into `GaloisForLFunctions/RHTower.lean` (or `HTGeometry.lean`); axiom-clean; warning-free.

## Corpus facts (checked; do NOT rebuild)

`CCMFirstRowStationaryPhase.lean` (ns `GaloisForLFunctions.RHTower`):
`xiSpeed s t = √((t²−s)/(t²−1))`, `xiCompSpeed`, `xiEndpointPhase = ∫_1^x xiSpeed`,
`integral_xiCompSpeed`, `xiSpeed_le_xiCompSpeed`, **`xiEndpointPhase_bounds`**,
`intervalIntegrable_xiSpeed`, `intervalIntegrable_rpow_sub_one` (integrability only — NOT the value),
`hasDerivAt_xiEndpointPhase`, `hasDerivAt_xiSpeed`, `continuousOn_xiSpeed`, `xiAmplitude`,
`xiAmplitude_le`.
`CCMFirstRowDunsterModel.lean`: `xiSpeed_pos`, `xiEndpointPhase_pos`.
`CCMFirstRowVanDerCorputBlocks.lean`: `one_le_xiSpeed`.
`CCMFirstRowEnvelopeTail.lean`: `continuousOn_xiAmplitude`, `continuousOn_xiEndpointPhase` (on `Ioi 1`).
`CCMRadialProlateDefect.lean`: `phaseLogDefect`, `abs_phaseLogDefect_le_far`.
`ProlateDunsterComparisonBridge.lean`: `xiAmplitudeDeriv`, `hasDerivAt_xiAmplitude`.

## What I built

- `RHTower/XiCoordinate.lean` — `xiEndpointPhase_one`, `continuousWithinAt_xiEndpointPhase_one`
  (continuity **at the singular endpoint**, by squeezing with the corpus bracket),
  `continuousOn_xiEndpointPhase_Ici`, **`strictMonoOn_xiEndpointPhase`**, `injOn_…`,
  `image_xiEndpointPhase_Icc/Ioo`, `xiEndpointPhase_le_two`,
  **`setIntegral_comp_xiEndpointPhase`**, **`intervalIntegral_comp_xiEndpointPhase`**
  (the substitution; proved on the OPEN interval via
  `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` — endpoint is a null set).
- `RHTower/XiTransportedPrimitive.lean` — `abs_integral_xiTransported_le` and
  `…_normalized_le`: `(45)` carried to the exterior variable; with the `√c` normalization the rate
  is `648M/c`.
- `RHTower/XiInverseCoordinate.lean` — `exists_lt_xiEndpointPhase`, `image_xiEndpointPhase_Ioi`,
  **`xiInverse`** (`Function.invFunOn` on `Ioi 1`), the two inverse laws, `strictMonoOn_xiInverse`,
  `image_xiInverse_Ioi`, `continuousAt_xiInverse`, **`hasDerivAt_xiInverse`**.
- `RHTower/XiBesselWeight.lean` — **`xiBesselWeight`** = the card's `(42)`, and
  **`xiAmplitude_mul_inv_xiSpeed_eq`** = the card's **`(41)`**.
- `RHTower/XiBesselWeightBounds.lean` — `xiBesselWeight_le_two`, `inv_le_xiBesselWeight(_of_le)`:
  the `C⁰` half of `(43)`.
- `HTGeometry/InverseSqrtEndpointIntegral.lean` — `rpow_neg_half_eq_inv_sqrt`,
  `integral_rpow_neg_half_sub_one`.
- `RHTower/XiEndpointExpansion.lean` — `xiEndpointFactor`, `xiSpeed_eq_factor_div`,
  `abs_xiEndpointFactor_sub_le`, `integral_inv_sqrt_sub_one`,
  `intervalIntegrable_inv_sqrt_sub_one`, `integral_sqrt_sub_one`, and
  **`abs_xiEndpointPhase_sub_leading_le`** = the card's **`(40)`**:
  `|ξ_s(x) − 2 g_s(1)√(x−1)| ≤ 2(x−1)^{3/2}`.

## Mathematical findings

1. The `C⁰` half of `(43)` needs **no** analytic expansion: the corpus bracket pins `r^{1/2}` to
   `(x²−1)^{1/4}` within a bounded factor, which cancels the apparent singularity in both directions.
2. The `C¹` half provably **cannot** come from the bracket: `B'/B` contains
   `x/(2√u√v) − 1/(2r)`, two terms each `~C/√u` whose difference is bounded only because their
   leading constants agree. That needs the next order — i.e. `(40)`, now proved.
3. `(40)` needs no analyticity: `g_s²` is rational and vanishes to first order at the endpoint, and
   `g_s ≥ 1/2` there, so the difference of squares gives the Lipschitz bound with no derivative of
   `g_s` ever computed.

## Remaining on this branch

The derivative bound on `B_σ` itself (assemble `(40)` + `hasDerivAt_xiInverse` + quotient rule),
then `(47)`; the `(48)` expansion *as an identity*; the `h₀,h₄` occupancy gate; the two RH-bearing
gates.

## Traps

- Root namespace `RHTower` vs `GaloisForLFunctions.RHTower` — cross-reference with `_root_.RHTower.…`.
- `IntervalIntegrable.congr` wants `EqOn` on `uIoc`, not an `ae` statement.
- `intervalIntegral.abs_integral_le_integral_abs` needs `(μ := volume)` given explicitly.
- `rw [show (1:ℝ) = √1 …]` rewrites *every* `1`, including inside other terms — use
  `Real.one_le_sqrt` instead.
- `rw [← hsq]` where `hsq : e^2 = 1/2` rewrites the `1/2` on both sides; rewrite inside a `have`
  instead of in the goal.
- Concurrent agents leave untracked, non-compiling modules in `HTGeometry/` (e.g. `PeelLimitVector`);
  the HTGeometry umbrella can be red through no fault of your own. Verify your own modules
  individually with `lake build <module>`.
