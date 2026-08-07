# Hedenmalm folder → stage 3: progress log (2026-08-07).  NOT FINISHED — 3 of 9 moved.

Goal: formalize unconditionally in Lean every proven statement in the 9 cards of
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.

## IN STAGE 3 (3 cards + companions)
1. `hedenmalm-quantile-volterra-universal-boundary-defect` — `(1)`–`(16)` newly formalized (9 modules).
2. `hedenmalm-reflection-folded-dirac-source-defect` — pre-existing Lean; audited, moved.
3. `hedenmalm-theta-flat-borel-holonomy-law` — pre-existing Lean; audited, moved.

## STILL IN STAGE 2 (6 cards)

### 4. `hedenmalm-prime-translation-rank-one-anomaly` — ALL ITS OWN CONTENT IS FORMALIZED
`RHTower/HedenmalmPrimeTranslationAnomaly.lean` + `RHTower/HedenmalmThetaSeriesExpansion.lean`
(card carries a `## Lean status` table).  Covered: `(3)`–`(18)`:
`sourceInverse_sourceShift` (7), `sourceInverse_integerShift` (8),
`shiftAnomaly_eq_zero_iff`/`integerAnomaly_eq_zero_iff`, `sourceEvaluation_integerShift` (10),
`hasDerivAt_sourceModeU` + `sourceModeU_equation` (11)/(24), `sourceInverse_sourceModeF` (12),
`ThetaSeriesSource` + `mellinTail_expChart` + `tail_eq_tsum_mellinTail` (13)/(14),
`sourceModeI_neg`/`sourceModeU_neg`/`sourceModeF_neg` + `conj_sourceModeI/U/F` (15),
`eq_of_sourceEquation` (16 geometric), `sourceEvaluationJet_integerShift` (18).
**BLOCKER TO MOVING:** the Jordan-*length* half of `(16)` is not this card's own proof — the card
says "analytic Fredholm multiplicity is the order `m` of `XiC`", i.e. it cites the multiplicity
clause of card 7 (`hedenmalm-theta-source-compressed-inverse-determinant`, statement `(6)`).
Once card 7's multiplicity clause is in Lean, card 4 moves.

### 6. `hedenmalm-supersymmetric-fredholm-range-divisor` — range-divisor half formalized
`RHTower/HedenmalmFredholmRangeDivisor.lean`: `cokernelVector`, `conj_cokernelVector_div`,
`integral_range_pairing` (5), `xiC_eq_zero_of_solution` (6⟹),
`twoEndedSolution_equation` + `hasDerivAt_twoEndedSolution` (6⟸/7),
`sourceModeI_eq_neg_tail_iff` + `setIntegral_Iic_add_Ioi` (7).
MISSING: weighted adjoint `(3)`, closedness + index `-1` `(4)`, compact resolvent, Witten square
`(8)`, supersymmetric Dirac `(9)`, strict positivity `(10)` — needs an unbounded-operator layer.

### 5. `hedenmalm-two-prime-theta-interval-normal-frame` — none; builds on module 4.
### 7. `hedenmalm-theta-source-compressed-inverse-determinant` — needs HS kernels, `det₂`, Hadamard.
   **Its multiplicity clause `(6)` is the blocker for card 4.**
### 8. `hedenmalm-essential-inverse-flow-prime-tomography` — none; punctured Riesz trace.
### 9. `hedenmalm-pair-weil-polarization-law` — one gate: Guinand–Weil test algebra in closed form.

## Next-session order
card 7 (unblocks 4) → card 5 → card 9 → card 8 → unbounded-operator half of card 6.

## Modules created in this session
`HTGeometry/WeightedDensityL2.lean`, `HTGeometry/PositiveDensityQuantile.lean`,
`HTGeometry/BoundedMultiplierHilbert.lean`, `RHTower/HedenmalmQuantileNormalForm.lean`,
`RHTower/HedenmalmQuantileMetric.lean`, `RHTower/HedenmalmQuantileBoundaryFlux.lean`,
`RHTower/HedenmalmQuantileRootMode.lean`, `RHTower/HedenmalmQuantileDivisorCharge.lean`,
`RHTower/HedenmalmPrimeTranslationAnomaly.lean`, `RHTower/HedenmalmFredholmRangeDivisor.lean`,
`RHTower/HedenmalmThetaSeriesExpansion.lean` — all wired into the umbrellas, all axiom-clean.

## Lean traps (v4.32)
- `AEStronglyMeasurable.div` needs `ContinuousDiv` (absent for ℂ) — use `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in context.
- Derivatives of `‖·‖²`: stay in ℂ (`HasDerivAt.star`, `conj w * w = ((‖w‖^2:ℝ):ℂ)`).
- `star` vs `starRingEnd ℂ`: defeq — `show` converts, `rw` does not.
- `Integrable.star` does not exist; `⟨conj∘f measurable, h.2.congr'⟩`.
- `Set.uIcc_subset_Ioo` does not exist — `Set.ordConnected_Ioo.uIcc_subset`.
- `rw [someDef]` fails for defs applied to arguments — use `show`.
- `integral_add_right_eq_self`, `Integrable.comp_add_right`, `integral_neg_eq_self` need
  `(μ := volume)` or explicit ascriptions.
- Annotate integral binders `∫ x : ℝ, …` when the integrand casts `x` to ℂ.
- Improper FTC: `integral_Iic_of_hasDerivAt_of_tendsto'`, `integral_of_hasDerivAt_of_tendsto`.
- Change of variables on a half-line: `integral_image_eq_integral_abs_deriv_smul` with
  `image_expChart`/`injOn_expChart` (proved in `HedenmalmThetaSeriesExpansion`).
- Termwise integration: `MeasureTheory.integral_tsum` (AEStronglyMeasurable + `∑' ∫⁻ ‖·‖ₑ ≠ ⊤`).
- `Real.exp_injective` breaks dependent elimination — use `Real.exp_eq_exp.mp` and
  `mul_left_cancel₀`.
- For `linear_combination … * hI` with `hI : I*I = -1`, expand `L - R` as a multiple of `(I²+1)`.
- Bash cwd persists; `cd formal` once, and re-`cd` after any `cd` to the repo root.
