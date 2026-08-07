# Hedenmalm folder → stage 3: progress log (2026-08-07).  NOT FINISHED — 3 of 9 moved.

Goal: formalize in Lean every proven statement of the 9 cards in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`3-formalized/new_scientific_knowledge/hedenmalm/` with an `<id>-formalized.md` companion.

## CHECK THESE CORPUS ASSETS BEFORE BUILDING ANYTHING
- `ContinuousLinearMap.IsHilbertSchmidt` — `HTGeometry/HilbertSchmidtOperator.lean:198`
- `IsHilbertSchmidt.isCompactOperator` — `HTGeometry/HilbertSchmidtCompact.lean:164`
- **`RHTower.isHilbertSchmidt_kernelOperator`** — `RHTower/SoninTimeBandHilbertSchmidt.lean:69`.
  Use for card 7 `(1)`.
- Determinants: only the DIAGONAL layer (`RHTower/ArithmeticDilationDeterminantZeros.lean`).
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder`
- `HTGeometry.QuantileCoupling.map_quantile_eq`; `MeasureTheory.lpBoundedMulCLM`

## IN STAGE 3 (3 cards + companions)
`hedenmalm-quantile-volterra-universal-boundary-defect` (all `(1)`–`(16)`),
`hedenmalm-reflection-folded-dirac-source-defect`, `hedenmalm-theta-flat-borel-holonomy-law`.

## STILL IN STAGE 2 — exact remaining items

### 4. `prime-translation-rank-one-anomaly` — OWN CONTENT COMPLETE `(3)`–`(18)`
Modules `HedenmalmPrimeTranslationAnomaly.lean`, `HedenmalmThetaSeriesExpansion.lean`.
ONLY BLOCKER: Jordan-length sentence of `(16)` cites card 7's analytic Fredholm multiplicity.

### 5. `two-prime-theta-interval-normal-frame` — `(3)`,`(4)`,`(5)`-mult,`(5a)`,`(6)`,`(7)` + two-prime
Module `RHTower/HedenmalmIntervalAnomaly.lean`:
`intervalMass`, `mass_mul_cdfFun_sub`, `integerAnomaly_eq_intervalMass` (4),
`intervalMass_add`, `integerAnomaly_mul` (5a),
`intervalMass_pos`, `centeredWindow`, `centeredWindow_eq`, `centeredWindow_pos`,
`cdfFun_neg`, `intervalMass_neg`, `centeredWindow_neg` (6),
`shiftMultiplier`, `shiftMultiplier_eq_zero_iff` (5-multiplier),
`centeredMultiplier`, `centeredMultiplier_eq`, `centeredMultiplier_eq_zero_iff` (7),
`pow_three_ne_pow_two`, `eq_zero_of_log_three_eq_log_two`, `no_common_zero_two_three`,
`no_common_zero_centered_two_three` (the headline two-prime theorem).
REMAINING: the factorization `hat r_n = q_n Ξ_C` (Fubini against the interval indicator:
`∫ r_n(x)e^{izx}dx = i n^{-1/2}∫∫ k(t)1_{t-L≤x<t}e^{izx}dx dt`), rapid decrease of `(6)`,
conormal generation, the two bounded self-adjoint channels, the essential compact-boundary symbol,
and the three frame obstructions (bounded corona, finite prime, summable all-prime).

### 6. `supersymmetric-fredholm-range-divisor` — range-divisor half done
`RHTower/HedenmalmFredholmRangeDivisor.lean`: `(5)`, `(6)`, `(7)`.
REMAINING: `(3)` weighted adjoint, `(4)` closedness + index `-1`, compact resolvent,
`(8)` Witten square, `(9)` supersymmetric Dirac, `(10)` strict positivity.
Needs an unbounded-Fredholm layer; mathlib has only `LinearPMap.adjoint`.

### 7. `theta-source-compressed-inverse-determinant` — `(4)`,`(5)`,`(6)`-pt-spectrum,`(7)` done
`RHTower/HedenmalmHilbertSchmidtNorm.lean`: `pinnedKernelSlice`,
`integral_pinnedKernelSlice_sq`, `tailEnergyDensity`, `integral_quantileSpeed_sq_slice` (5),
`sourceReflection`, `sourceInverse_sourceReflection` (7),
`xiC_eq_zero_of_solution_const` (6⟹), `sourceInverse_sourceModeF_eq_smul` (6⟸),
`sourceEvaluation_k` (Grushin scalar corner).
REMAINING: `(1)` assembled HS operator (use `isHilbertSchmidt_kernelOperator`);
`(6)` **multiplicity clause** — analytic Fredholm multiplicity + Grushin reduction to
`diag(I, Ξ_C)`; unblocks card 4.  `(8)` `det₂`.  `(9)` `tr(B²)` = variance
(2-D Fubini: `∫∫_{x<y}p(x)(1-p(y)) dxdy = E[(X-X')²]/4`).

### 8. `essential-inverse-flow-prime-tomography` — none; punctured Riesz trace, von Mangoldt weld.
### 9. `pair-weil-polarization-law` — one gate: Guinand–Weil test algebra in closed form.

## Recommended next order
card 5 remainder → card 9 → card 7 `(9)` → card 8 → then the three foundational builds
(analytic Fredholm multiplicity, `det₂`, unbounded Fredholm), which are the only genuinely large
pieces left.

## Modules created this session (14, all wired, all axiom-clean, all building)
`HTGeometry/`: `WeightedDensityL2`, `PositiveDensityQuantile`, `BoundedMultiplierHilbert`.
`RHTower/`: `HedenmalmQuantileNormalForm`, `HedenmalmQuantileMetric`,
`HedenmalmQuantileBoundaryFlux`, `HedenmalmQuantileRootMode`, `HedenmalmQuantileDivisorCharge`,
`HedenmalmPrimeTranslationAnomaly`, `HedenmalmFredholmRangeDivisor`,
`HedenmalmThetaSeriesExpansion`, `HedenmalmHilbertSchmidtNorm`, `HedenmalmIntervalAnomaly`.

## Lean traps (v4.32)
- `AEStronglyMeasurable.div` needs `ContinuousDiv` (absent for ℂ) — `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in context; check whether a trailing `ring` is needed.
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
- `Measure.integrableOn_of_bounded` names its bound `M`; `setIntegral_const` yields `Measure.real`.
- `Real.exp_injective` breaks dependent elimination — `Real.exp_eq_exp.mp` + `mul_left_cancel₀`.
- `Nat.pos_iff.mp` does not exist — use `h.ne'`.
- `simp` rewrites `((Real.log ((3:ℕ):ℝ) : ℝ) : ℂ)` into `Complex.log 3`; go through
  `Complex.ofReal_inj` instead when moving a real identity out of ℂ.
- **`linear_combination` against `hI : I*I = -1`: never guess the coefficient.  Read the residual
  goal, factor it as `c · (I² + 1)`, and use `c`.**  Same for `hexp`-style side relations.
- Bash cwd persists; `cd formal` once, and re-`cd` after any `cd` to the repo root.

## Update — unconditional instantiation built (2026-08-07, later)

New module `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceUnconditional.lean`
(wired into `RHTower.lean`, compiles clean).  It closes the "everything is stated over a
hypothesis class" objection:

- `thetaCuspFullSource_pos : ∀ x, 0 < thetaCuspFullSource x`  (new global positivity: `>0` half
  from `thetaCuspFullSource_pos_of_pos`, `<0` half from `thetaCuspFullSource_neg`, seam from
  `thetaCuspFullSource_zero_pos_for_cold_seam`).
- `thetaSource : PositiveDensitySource` — k := `thetaCuspFullSource`,
  continuity from `contDiff_thetaCuspFullSource`, integrability from `thetaCuspSchwartzReal`.
- `thetaSource_even`, `thetaBound := thetaCuspDerivativeExpConstant 0`, `thetaSource_le`,
  `tendsto_thetaSource_atBot/atTop`.
- `hasShiftedTail_thetaSource : |z.im| < 1 → HasShiftedTail thetaSource z`.
- `xiC_thetaSource : |z.im| < 1 → xiC thetaSource z = XiC z`
  (via `thetaCuspFourierLaplace_eq_XiC_on_strip` at `-z`, then `XiC_even`).
- `thetaMetricOperator` + `denseRange_thetaMetricOperator`,
  `not_boundedBelow_thetaMetricOperator`, `inner_thetaMetricOperator_quantileUnitary`.
- Unconditional card forms: `sourceInverse_sourceReflection_theta` (RBR = -B),
  `XiC_eq_zero_of_solution`, `sourceModeI_eq_neg_tail_iff_XiC`, `sourceModeI_neg_theta`,
  `intervalMass_neg_theta`, `centeredWindow_neg_theta`.

Card 7 statement (1) chain finished in `HedenmalmHilbertSchmidtNorm.lean`:
`norm_sq_pinnedSliceVec`, `pinnedKernelField`, `pinnedKernelField_apply`,
`norm_pinnedKernelField`, `continuousOn_quantileSpeed`, `continuousOn_pinnedKernelField`,
`aestronglyMeasurable_pinnedKernelField`, `HasFiniteKernelEnergy`, `memLp_pinnedKernelField`,
`pinnedKernelL2`, `isHilbertSchmidt_pinnedKernelOperator`,
`isCompactOperator_pinnedKernelOperator`.

### The one remaining analytic obligation of statement (1)
`HasFiniteKernelEnergy thetaSource`, i.e. `∫₀¹ q² t(1-t) dt = M ∫ p(1-p)/k < ∞`.
PROVEN ROUTE (elementary, no Gamma integrals needed), for x ≥ 1:
1. upper: `k(y) ≤ (1+W)·4π² e^{9y/2} e^{-π e^{2y}}` for y ≥ 0
   (`thetaCuspFullSource_sub_first_le` + `2πt⁴ - 3t² ≤ 2πt⁴`).
2. lower: `k(x) ≥ 2π² e^{9x/2} e^{-π e^{2x}}` for x ≥ 0
   (term₁ ≤ tsum since all terms ≥ 0, and `2πe^{4x} - 3e^{2x} ≥ π e^{4x}` for x ≥ 0).
3. convexity `e^{2y} ≥ e^{2x}(1 + 2(y-x))` for y ≥ x, so
   `e^{-πe^{2y}} ≤ e^{-πe^{2x}} e^{-2π e^{2x}(y-x)}`.
4. for x ≥ 1, `2πe^{2x} - 9/2 ≥ πe^{2x}`, so `∫_x^∞ k ≤ C e^{9x/2}e^{-πe^{2x}}/(π e^{2x})`.
5. divide: `(1-p(x))/k(x) ≤ C' e^{-2x}` on `[1,∞)`; evenness gives `[-∞,-1]`; the middle is
   continuous on a compact.
Do NOT try `k = H'` in closed form — the elementary primitive leaves a `+1/4 e^{x/2}θ̃` residue
(this is the `(D² - 1/4)` of the reflection law), so it does not close.
