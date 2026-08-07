# Hedenmalm folder → stage 3: progress log (2026-08-07).  NOT FINISHED — 3 of 9 moved.

Task: formalize unconditionally in Lean every proven statement in the 9 cards of
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.

## IN STAGE 3 (3 cards, each with a companion certificate)

1. `hedenmalm-quantile-volterra-universal-boundary-defect` — all of `(1)`–`(16)` newly formalized.
2. `hedenmalm-reflection-folded-dirac-source-defect` — pre-existing Lean; audited and moved.
3. `hedenmalm-theta-flat-borel-holonomy-law` — pre-existing Lean; audited and moved.

## STILL IN STAGE 2 (6 cards)

### 4. `hedenmalm-prime-translation-rank-one-anomaly` — PARTIALLY FORMALIZED
Module `RHTower/HedenmalmPrimeTranslationAnomaly.lean` (builds, wired, axiom-clean) now has a
`## Lean status` table on the card.  Formalized: `(3)`–`(12)`, `(17)`, `(18)` —
`sourceInverse_sourceShift` (7), `sourceInverse_integerShift` (8),
`shiftAnomaly_eq_zero_iff` / `integerAnomaly_eq_zero_iff` (nonvanishing),
`sourceEvaluation_integerShift` (10), `hasDerivAt_sourceModeU` + `sourceModeU_equation` (11)/(24),
`sourceInverse_sourceModeF` (12), `sourceEvaluationJet_integerShift` (18).
**Missing:** `(14)` integer Mellin expansion (needs the theta series of `k`, not just positivity);
`(15)` reflection package (needs an evenness hypothesis + a set-reflection change of variables:
`∫_{Iic(-x)} k(y)e^{-izy} = xiC z - ∫_{Iic x} k e^{izy}`); `(16)` `dim ker = 1` — **blocked on card 6**
(it quotes the parent Fredholm theorem).

### 5. `hedenmalm-two-prime-theta-interval-normal-frame` — none
Needs: integrated rank-one anomaly over a theta interval, `a_n XiC` factorization, sinc multipliers
for `log 2`/`log 3` with no common zero, frame obstructions.  Builds directly on module 4.

### 6. `hedenmalm-supersymmetric-fredholm-range-divisor` — none (`[OPEN]` on the card)
The keystone: unbounded weighted first-order operator on `L²(ℝ,k⁻¹dx)`, closed range, Fredholm
index, exact `Xi` cokernel coordinate, Witten square.  Cards 4 `(16)`, 5 and 7 depend on it.

### 7. `hedenmalm-theta-source-compressed-inverse-determinant` — only `HTGeometry.SourceGrushinInverse`
Needs Hilbert–Schmidt integral operators with kernels, the regularized determinant `det₂`, and the
genus-one Hadamard product.  mathlib has none of these.

### 8. `hedenmalm-essential-inverse-flow-prime-tomography` — none
Needs the punctured Riesz trace of the essential inverse flow and the von Mangoldt weld.

### 9. `hedenmalm-pair-weil-polarization-law` — large existing Lean, ONE open gate
Extend the prime+Gamma equality from the Cauchy/resolvent core (`XiWeilResolventSource`,
`primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace`) to the **full Guinand–Weil test algebra
in closed form**.  All other gates are checked.

## Recommended order for the next session
6 → 7 → 4-remainder → 5 → 8 → 9 (card 6 unblocks 4, 5 and 7).

## Reusable infrastructure built here

- `HTGeometry/PositiveDensityQuantile.lean`: `structure PositiveDensitySource`; `mass`,
  `normalized`, `law`, `cdfFun` (C¹, derivative `k/M`, `strictMono_cdfFun`, `cdfFun_mem_Ioo`,
  `surjOn_cdfFun`), `quantileFun` (`quantile_cdfFun`, `cdfFun_quantile`), both transport laws,
  `integrable_law_iff`, `integrableOn_comp_quantileFun_iff`, witness `gaussianSource`.
- `HTGeometry/WeightedDensityL2.lean`: `weightedDensityUnitary : L²(μ.withDensity w) ≃ₗᵢ L²(μ)`.
- `HTGeometry/BoundedMultiplierHilbert.lean`: general-measure self-adjointness / injectivity /
  dense range for `lpBoundedMulCLM`.
- `RHTower/HedenmalmQuantile*`: `quantileUnitary`, `sourceInverse`, `sourceChar`, `xiC`,
  `HasShiftedTail`, `quantileSpeed`, `metricSymbol`, `metricOperator`, `rootH`/`rootG`/`rootA`,
  `hasDerivAt_quantileFun`.
- `RHTower/HedenmalmPrimeTranslationAnomaly.lean`: `setIntegral_Iic_comp_sub/_add`,
  `hasDerivAt_setIntegral_Iic` (FTC for `Iic`-primitives), `sourceEvaluationJet`.

## Lean traps (v4.32)

- `AEStronglyMeasurable.div` needs `ContinuousDiv`, absent for ℂ — use `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in context; substituting `(M:ℂ) = √M*√M` first closes the
  mass algebra.
- Stay in ℂ for derivatives of `‖·‖²`: use `HasDerivAt.star` and `conj w * w = ((‖w‖^2:ℝ):ℂ)`;
  `Complex.reCLM.hasFDerivAt.comp_hasDerivAt` fails on ℝ-target instance paths.
- `star` vs `starRingEnd ℂ` are defeq — `show` converts, `rw` does not.
- `Integrable.star` does not exist; `⟨conj∘f measurable, h.2.congr'⟩`.
- `Set.uIcc_subset_Ioo` does not exist — `Set.ordConnected_Ioo.uIcc_subset`.
- `rw [someDef]` fails for defs applied to arguments — use `show`.
- `integral_add_right_eq_self` / `Integrable.comp_add_right` need `(μ := volume)` or explicit type
  ascriptions, else instance search gets stuck.
- Annotate integral binders `∫ x : ℝ, …` when the integrand casts `x` to ℂ.
- `MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'` is the improper FTC on `Iic`.
- Bash cwd persists between calls: `cd formal` once; after any `cd` to the repo root, greps against
  `GaloisForLFunctions/...` silently return nothing.
