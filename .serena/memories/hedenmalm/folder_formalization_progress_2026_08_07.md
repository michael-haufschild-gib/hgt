# Hedenmalm folder → stage 3: progress log (2026-08-07)

Task: formalize unconditionally in Lean every proven statement in the 9 cards of
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.

## DONE — 3 of 9 moved to stage 3

1. **`hedenmalm-quantile-volterra-universal-boundary-defect`** — every numbered statement
   `(1)`–`(16)` newly formalized.  New modules:
   - `HTGeometry/WeightedDensityL2.lean` — `weightedDensityUnitary : L²(μ.withDensity w) ≃ₗᵢ L²(μ)`.
   - `HTGeometry/PositiveDensityQuantile.lean` — `structure PositiveDensitySource`; `p` is C¹ with
     derivative `k/M`, strictly mono onto `(0,1)`, `Q` two-sided inverse, both transport laws,
     `integrable_law_iff`, `integrableOn_comp_quantileFun_iff`, witness `gaussianSource`.
   - `HTGeometry/BoundedMultiplierHilbert.lean` — measure-agnostic self-adjoint/injective/dense
     range for `lpBoundedMulCLM`.
   - `RHTower/HedenmalmQuantileNormalForm.lean` — `quantileUnitary` (1)(2), change of variables,
     `quantileTransform_sourceInverse(_eq_pinned)` = `T = i M_q C` (3), `quantileMetric_pullback` (4a).
   - `RHTower/HedenmalmQuantileMetric.lean` — `metricOperator` (4), `not_boundedBelow_metricOperator`,
     `inner_metricOperator_quantileUnitary` (4a), multiplier scope for (5a).
   - `RHTower/HedenmalmQuantileBoundaryFlux.lean` — (6)(7)(15)(16), ±1/√12 eigenvalues, flux law (8).
   - `RHTower/HedenmalmQuantileRootMode.lean` — `hasDerivAt_quantileFun` (Q'=q), `xiC`, (9)(10)(11).
   - `RHTower/HedenmalmQuantileDivisorCharge.lean` — (12)(13)(14).
   Two named hypotheses, documented in the companion: `HasShiftedTail S z`, `RootModeEndpoints S z`.
2. **`hedenmalm-reflection-folded-dirac-source-defect`** — already fully formalized by earlier
   sessions; audited (all 30+ names resolve, 20 `#print axioms` clean) and moved.
3. **`hedenmalm-theta-flat-borel-holonomy-law`** — already fully formalized; audited (51/53 backticked
   names resolve, the 2 exceptions are an open-core marker and a math symbol; 12 axioms clean) and
   moved.

## REMAINING 6 CARDS

| card | Lean state | missing machinery |
|---|---|---|
| `hedenmalm-pair-weil-polarization-law` | large | ONE gate: extend the prime+Gamma equality from the Cauchy/resolvent core to the **full Guinand–Weil test algebra in closed form** (Weil explicit formula for a general test function).  Corpus already has `primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace` and `XiWeilResolventSource.lean`, `XiWeilHilbertCore.lean`, `XiQuotientRealDecay.lean`, `XiHorizontalStripDecay.lean`. |
| `hedenmalm-theta-source-compressed-inverse-determinant` | `HTGeometry.SourceGrushinInverse` only | Hilbert–Schmidt integral operators, regularized determinant `det₂`, Hadamard genus-one product |
| `hedenmalm-supersymmetric-fredholm-range-divisor` | **none** (`[OPEN]`) | unbounded weighted first-order operator, closed range, Fredholm index, Witten square |
| `hedenmalm-essential-inverse-flow-prime-tomography` | none | punctured Riesz trace, essential inverse flow, von Mangoldt weld |
| `hedenmalm-prime-translation-rank-one-anomaly` | none | rank-one commutator with the source inverse, Jordan length |
| `hedenmalm-two-prime-theta-interval-normal-frame` | none | sinc multipliers for log 2 / log 3, no common zero, frame obstruction |

## Key reusable discoveries

- `HTGeometry.QuantileCoupling.map_quantile_eq` is inverse-transform sampling; mathlib has no
  probability-integral transform.
- `MeasureTheory.lpBoundedMulCLM` (`HTGeometry/LpBoundedMultiplier.lean`) = bounded multiplication
  operator; general-measure self-adjointness/dense-range now in `BoundedMultiplierHilbert`.
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder` = residue of a
  logarithmic derivative is the meromorphic order.
- `RHTower.unitIntervalMeasure_eq : unitIntervalMeasure = volume.restrict (Ioo 0 1)` (new).

## Lean traps hit (v4.32)

- `AEStronglyMeasurable.div` needs `ContinuousDiv`, absent for ℂ — use `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in the local context.
- Substituting `(M:ℂ) = √M*√M` (`rw [← hMM]`) before `field_simp` closes the mass algebra.
- `Complex.reCLM.hasFDerivAt.comp_hasDerivAt` fails on ℝ-target instance paths; stay in ℂ using
  `HasDerivAt.star` and `conj w * w = ((‖w‖^2 : ℝ) : ℂ)`.
- `star` vs `starRingEnd ℂ` are defeq: `show` converts, `rw` does not.
- `Integrable.star` does not exist; build it as `⟨conj∘f measurable, h.2.congr'⟩`.
- `Set.uIcc_subset_Ioo` does not exist; use `Set.ordConnected_Ioo.uIcc_subset`.
- The Bash tool's cwd persists across calls — `cd formal` once, and re-`cd` after any `cd` to the
  repo root, or greps silently return nothing.
