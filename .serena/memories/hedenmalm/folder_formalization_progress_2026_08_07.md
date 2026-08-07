# Hedenmalm folder → stage 3: progress log (2026-08-07).  NOT FINISHED — 3 of 9 moved.

Goal: formalize unconditionally in Lean every proven statement in the 9 cards of
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.

## CORPUS ASSETS TO REUSE — CHECK THESE BEFORE BUILDING ANYTHING
- `ContinuousLinearMap.IsHilbertSchmidt` — `HTGeometry/HilbertSchmidtOperator.lean:198`.
- `IsHilbertSchmidt.isCompactOperator` — `HTGeometry/HilbertSchmidtCompact.lean:164`.
- **`RHTower.isHilbertSchmidt_kernelOperator`** (`RHTower/SoninTimeBandHilbertSchmidt.lean:69`):
  an `Lp (E →L[ℂ] ℂ) 2 μ` field of continuous functionals induces a genuinely Hilbert–Schmidt
  `kernelOperator μ K`.  **This is the tool for card 7 statement (1)** — do not rebuild it.
- `HTGeometry/HilbertSchmidtMatrix.lean`, `HilbertSchmidtRectangular.lean`, `L2PairingEnergy.lean`,
  `TwoProjectionHilbertSchmidtEnergy.lean`.
- Fredholm determinants: only the **diagonal** product layer exists
  (`RHTower/ArithmeticDilationDeterminantZeros.lean`: entire, factorization, zero classification).
  No general `det₂` in the corpus or mathlib — that is a genuine build for card 7 statement (8).
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder`.
- `HTGeometry.QuantileCoupling.map_quantile_eq` (inverse-transform sampling).
- `MeasureTheory.lpBoundedMulCLM` (`HTGeometry/LpBoundedMultiplier.lean`).

## IN STAGE 3 (3 cards + companions)
1. `hedenmalm-quantile-volterra-universal-boundary-defect` — `(1)`–`(16)` newly formalized.
2. `hedenmalm-reflection-folded-dirac-source-defect` — audited, moved.
3. `hedenmalm-theta-flat-borel-holonomy-law` — audited, moved.

## STILL IN STAGE 2 (6 cards)

### 4. `hedenmalm-prime-translation-rank-one-anomaly` — ITS OWN CONTENT IS COMPLETE
`RHTower/HedenmalmPrimeTranslationAnomaly.lean` + `RHTower/HedenmalmThetaSeriesExpansion.lean`
cover `(3)`–`(18)`.  BLOCKER: the Jordan-*length* sentence in `(16)` cites card 7's analytic
Fredholm multiplicity (statement `(6)`), which has no Lean.  Card 4 moves as soon as that exists.

### 7. `hedenmalm-theta-source-compressed-inverse-determinant` — STARTED
`RHTower/HedenmalmHilbertSchmidtNorm.lean` (new): `pinnedKernelSlice`,
`integral_pinnedKernelSlice_sq` (inner slice energy `t(1-t)`),
`tailEnergyDensity`, `integral_quantileSpeed_sq_slice`
(`∫₀¹ q² t(1-t) = M ∫ p(1-p)/k` — the theta-tail form of statement `(5)`).
NEXT: assemble the kernel operator via `isHilbertSchmidt_kernelOperator` for `(1)`/`(4)`;
then `(6)` point spectrum (the two directions already exist as
`HedenmalmPrimeTranslation.sourceInverse_sourceModeF` and
`HedenmalmFredholmRange.xiC_eq_zero_of_solution`); then the multiplicity clause of `(6)`
(the Grushin reduction to `diag(I, Ξ_C)`), which unblocks card 4; then `(7)` `RBR = -B`,
`(8)` `det₂ = Ξ_C/Ξ_C(0)` (needs a `det₂` build), `(9)` `tr(B²) = variance`, `(10)`.

### 6. `hedenmalm-supersymmetric-fredholm-range-divisor` — range-divisor half formalized
`RHTower/HedenmalmFredholmRangeDivisor.lean`: `(5)`, `(6)`, `(7)`.
MISSING: weighted adjoint `(3)`, closedness + index `-1` `(4)`, compact resolvent, Witten square
`(8)`, supersymmetric Dirac `(9)`, strict positivity `(10)` — unbounded-operator layer.

### 5. `hedenmalm-two-prime-theta-interval-normal-frame` — none; builds on module 4.
### 8. `hedenmalm-essential-inverse-flow-prime-tomography` — none; punctured Riesz trace.
### 9. `hedenmalm-pair-weil-polarization-law` — one gate: Guinand–Weil test algebra in closed form.

## Next-session order
finish card 7 (kernel operator + multiplicity ⇒ unblocks card 4) → card 5 → card 9 → card 8 →
unbounded-operator half of card 6.

## Modules created this session (all wired, all axiom-clean)
`HTGeometry/WeightedDensityL2.lean`, `HTGeometry/PositiveDensityQuantile.lean`,
`HTGeometry/BoundedMultiplierHilbert.lean`, `RHTower/HedenmalmQuantileNormalForm.lean`,
`RHTower/HedenmalmQuantileMetric.lean`, `RHTower/HedenmalmQuantileBoundaryFlux.lean`,
`RHTower/HedenmalmQuantileRootMode.lean`, `RHTower/HedenmalmQuantileDivisorCharge.lean`,
`RHTower/HedenmalmPrimeTranslationAnomaly.lean`, `RHTower/HedenmalmFredholmRangeDivisor.lean`,
`RHTower/HedenmalmThetaSeriesExpansion.lean`, `RHTower/HedenmalmHilbertSchmidtNorm.lean`.

## Lean traps (v4.32)
- `AEStronglyMeasurable.div` needs `ContinuousDiv` (absent for ℂ) — use `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in context; drop the trailing `ring` when it closes.
- Derivatives of `‖·‖²`: stay in ℂ (`HasDerivAt.star`, `conj w * w = ((‖w‖^2:ℝ):ℂ)`).
- `star` vs `starRingEnd ℂ`: defeq — `show` converts, `rw` does not.
- `Integrable.star` does not exist; `⟨conj∘f measurable, h.2.congr'⟩`.
- `Set.uIcc_subset_Ioo` does not exist — `Set.ordConnected_Ioo.uIcc_subset`.
- `rw [someDef]` fails for defs applied to arguments — use `show`.
- `integral_add_right_eq_self`, `Integrable.comp_add_right`, `integral_neg_eq_self` need
  `(μ := volume)` or explicit ascriptions.
- Annotate integral binders `∫ x : ℝ, …` when the integrand casts `x` to ℂ.
- Improper FTC: `integral_Iic_of_hasDerivAt_of_tendsto'`, `integral_of_hasDerivAt_of_tendsto`.
- Half-line change of variables: `integral_image_eq_integral_abs_deriv_smul` +
  `HedenmalmThetaSeries.image_expChart`/`injOn_expChart`.
- Termwise integration: `MeasureTheory.integral_tsum`.
- `Measure.integrableOn_of_bounded` names its bound `M`, not `C`; `setIntegral_const` produces
  `Measure.real`, so `rw [Measure.real, Real.volume_Ioc]`.
- `Real.exp_injective` breaks dependent elimination — `Real.exp_eq_exp.mp` + `mul_left_cancel₀`.
- For `linear_combination … * hI` with `hI : I*I = -1`, expand `L - R` as a multiple of `(I²+1)`.
- Bash cwd persists; `cd formal` once, and re-`cd` after any `cd` to the repo root.
