# Hedenmalm folder → stage 3: progress log (2026-08-07).  NOT FINISHED — 3 of 9 moved.

Goal: formalize in Lean every proven statement in the 9 cards of
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`3-formalized/new_scientific_knowledge/hedenmalm/` with an `<id>-formalized.md` companion.

## CHECK THESE CORPUS ASSETS BEFORE BUILDING ANYTHING
- `ContinuousLinearMap.IsHilbertSchmidt` — `HTGeometry/HilbertSchmidtOperator.lean:198`
- `IsHilbertSchmidt.isCompactOperator` — `HTGeometry/HilbertSchmidtCompact.lean:164`
- **`RHTower.isHilbertSchmidt_kernelOperator`** — `RHTower/SoninTimeBandHilbertSchmidt.lean:69`
  (`Lp (E →L[ℂ] ℂ) 2 μ` field ⇒ genuine HS `kernelOperator`).  Use for card 7 `(1)`.
- Determinants: only the DIAGONAL product layer
  (`RHTower/ArithmeticDilationDeterminantZeros.lean`).  No general `det₂` → genuine build.
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder`
- `HTGeometry.QuantileCoupling.map_quantile_eq`; `MeasureTheory.lpBoundedMulCLM`

## IN STAGE 3 (3 cards + companions)
`hedenmalm-quantile-volterra-universal-boundary-defect` (all `(1)`–`(16)`),
`hedenmalm-reflection-folded-dirac-source-defect`, `hedenmalm-theta-flat-borel-holonomy-law`.

## STILL IN STAGE 2

### 4. `prime-translation-rank-one-anomaly` — OWN CONTENT COMPLETE `(3)`–`(18)`
Modules: `HedenmalmPrimeTranslationAnomaly.lean`, `HedenmalmThetaSeriesExpansion.lean`.
BLOCKER: Jordan-length sentence of `(16)` cites card 7's analytic Fredholm multiplicity.

### 5. `two-prime-theta-interval-normal-frame` — `(3)`,`(4)`,`(5a)`,`(6)` done
Module `RHTower/HedenmalmIntervalAnomaly.lean`: `intervalMass`, `mass_mul_cdfFun_sub`,
`integerAnomaly_eq_intervalMass` (4), `intervalMass_add` + `integerAnomaly_mul` (5a),
`intervalMass_pos`, `centeredWindow`, `centeredWindow_eq`, `centeredWindow_pos`,
`cdfFun_neg`, `intervalMass_neg`, `centeredWindow_neg` (6: positive, real, even).
REMAINING: `(5)` `hat r_n = q_n Ξ_C` — Fubini against the interval indicator:
`∫ r_n(x)e^{izx}dx = i n^{-1/2}∫∫ k(t)1_{t-L≤x<t}e^{izx}dxdt = n^{-1/2}(1-e^{-izL})/z · Ξ_C(z)`;
decay of `(6)`; multiplier `(7)`; **two-prime no-common-zero** (see sketch below);
conormal generation; two self-adjoint channels; essential symbol; three frame obstructions.

SKETCH for two-prime no-common-zero (do not re-derive):
`q_n(z)=0`, `z≠0` ⟺ `exp(-i z log n)=1` ⟺ `-i z log n = 2πI j` for some `j : ℤ` ⟺
`z = -2π j / log n`.  A common nonzero zero for `n=2,3` gives `j log 3 = k log 2`, i.e.
`3^j = 2^k` in ℤ, hence `j=k=0` hence `z=0`.  Key mathlib: `Complex.exp_eq_one_iff`.

### 6. `supersymmetric-fredholm-range-divisor` — range-divisor half done
`RHTower/HedenmalmFredholmRangeDivisor.lean`: `(5)`, `(6)`, `(7)`.
REMAINING: `(3)` adjoint, `(4)` index `-1`, compact resolvent, `(8)` Witten square, `(9)` Dirac,
`(10)` strict positivity — needs an unbounded-Fredholm layer (mathlib has only `LinearPMap.adjoint`).

### 7. `theta-source-compressed-inverse-determinant` — `(4)`,`(5)`,`(6)`-point-spectrum,`(7)` done
`RHTower/HedenmalmHilbertSchmidtNorm.lean`: `pinnedKernelSlice`,
`integral_pinnedKernelSlice_sq`, `tailEnergyDensity`, `integral_quantileSpeed_sq_slice` (5),
`sourceReflection` + `sourceInverse_sourceReflection` (7),
`xiC_eq_zero_of_solution_const` (6⟹), `sourceInverse_sourceModeF_eq_smul` (6⟸),
`sourceEvaluation_k` (Grushin scalar corner `ℓ_z(k)=Ξ_C(z)`).
REMAINING: `(1)` assembled HS operator; `(6)` **multiplicity clause** (analytic Fredholm
multiplicity + Grushin reduction to `diag(I, Ξ_C)`) — unblocks card 4; `(8)` `det₂`;
`(9)` `tr(B²)` = variance (2-D Fubini: `∫∫_{x<y}p(x)(1-p(y)) = E[(X-X')²]/4`).

### 8. `essential-inverse-flow-prime-tomography` — none; punctured Riesz trace.
### 9. `pair-weil-polarization-law` — one gate: Guinand–Weil test algebra, closed form.

## Recommended next order
card 5 remainder (no infrastructure blocker) → card 9 → card 7 `(9)` → card 8 →
then the three big builds: analytic multiplicity, `det₂`, unbounded Fredholm.

## Modules created this session (14, all wired, all axiom-clean)
`HTGeometry/`: `WeightedDensityL2`, `PositiveDensityQuantile`, `BoundedMultiplierHilbert`.
`RHTower/`: `HedenmalmQuantileNormalForm`, `HedenmalmQuantileMetric`,
`HedenmalmQuantileBoundaryFlux`, `HedenmalmQuantileRootMode`, `HedenmalmQuantileDivisorCharge`,
`HedenmalmPrimeTranslationAnomaly`, `HedenmalmFredholmRangeDivisor`,
`HedenmalmThetaSeriesExpansion`, `HedenmalmHilbertSchmidtNorm`, `HedenmalmIntervalAnomaly`.

## Lean traps (v4.32)
- `AEStronglyMeasurable.div` needs `ContinuousDiv` (absent for ℂ) — `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in context; sometimes needs a trailing `ring`, sometimes
  closes on its own — check before adding one.
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
- For `linear_combination … * hI` with `hI : I*I = -1`, expand `L - R` as a multiple of `(I²+1)`;
  the sign is easy to get wrong — read the residual goal and solve for the coefficient.
- Bash cwd persists; `cd formal` once, and re-`cd` after any `cd` to the repo root.
