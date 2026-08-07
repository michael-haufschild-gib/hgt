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
