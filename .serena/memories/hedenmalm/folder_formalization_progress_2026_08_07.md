# Hedenmalm folder → stage 3: progress log (started 2026-08-07)

Task: formalize unconditionally in Lean every proven theorem in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/` (9 cards), then move each
card to `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.

## Card inventory and Lean state at start

| card | Lean at start |
|---|---|
| `hedenmalm-quantile-volterra-universal-boundary-defect` | `HedenmalmPinnedVolterraBoundaryDefect` only (universal half) |
| `hedenmalm-theta-source-compressed-inverse-determinant` | `HTGeometry.SourceGrushinInverse` (bounded algebraic core only) |
| `hedenmalm-pair-weil-polarization-law` | large (`XiWeil*`, `XiTheta*`); one open Lean gate: Guinand–Weil closed form |
| `hedenmalm-reflection-folded-dirac-source-defect` | large (`XiHedenmalmReflectionFoldedDirac` etc.) |
| `hedenmalm-theta-flat-borel-holonomy-law` | large (`XiHedenmalmThetaBorel*`, `BurnolCoPoisson*`) |
| `hedenmalm-supersymmetric-fredholm-range-divisor` | **none** (`[OPEN]`, needs unbounded weighted operators) |
| `hedenmalm-essential-inverse-flow-prime-tomography` | none |
| `hedenmalm-prime-translation-rank-one-anomaly` | none |
| `hedenmalm-two-prime-theta-interval-normal-frame` | none |

## DONE — quantile card (moved to stage 3)

New modules (all build, only `propext`/`Classical.choice`/`Quot.sound`):

- `HTGeometry/WeightedDensityL2.lean` — general unitary `L²(μ.withDensity w) ≃ₗᵢ L²(μ)`,
  `f ↦ √w·f`, for measurable everywhere-positive `w`.  Key names: `realDensity`, `sqrtWeight`,
  `memLp_two_withDensity_iff`, `weightedDensityUnitary`, `densityMul_ae`, `densityDiv_ae`.
- `HTGeometry/PositiveDensityQuantile.lean` — `structure PositiveDensitySource` (k continuous,
  positive, integrable); `mass`, `normalized`, `law`, `cdfFun`, `quantileFun`.  Proves `p` is C¹
  with derivative `k/M`, strictly mono, range `(0,1)`, `Q` two-sided inverse, and BOTH transport
  laws (`measurePreserving_quantileFun`, `measurePreserving_cdfFun`).  Witness `gaussianSource`.
- `HTGeometry/BoundedMultiplierHilbert.lean` — measure-agnostic self-adjointness/injectivity/dense
  range of `lpBoundedMulCLM`.
- `RHTower/HedenmalmQuantileNormalForm.lean` — `SourceSpace S = L²(ℝ,k⁻¹dx)`, `quantileUnitary`
  (statement (1)/(2)), change of variables `integral_comp_quantile` /
  `setIntegral_comp_quantile`, `integrable_sourceSpace`, `sourceInverse`,
  `quantileTransform_sourceInverse` and `..._eq_pinned` (statement (3) `T = i M_q C`),
  `quantileMetric_pullback` (4a).
- `RHTower/HedenmalmQuantileMetric.lean` — `metricOperator` (`G = M_{1/q}`) bounded/injective/
  self-adjoint/dense-range/`not_boundedBelow_metricOperator`,
  `inner_metricOperator_quantileUnitary` (4a inner form),
  `isPinnedPointwiseMultiplier_lpBoundedMulCLM` + `eq_zero_of_anticommutator` (scope of (5a)).

STILL TO DO on this card (statements (6)–(16) of the paper card, not yet in Lean):
(7) `⟪R₂g,g⟫ = -2Re(c(g)·conj m(g))`; (8) eigen-relation flux law; (9) explicit root mode;
(10) `∫₀¹ exp(izQ(u))du = M⁻¹ Ξ_C(z)` — this one is a one-line corollary of
`integral_comp_quantile` with `g x = exp(izx)`; (11) ordered-correlation flux; (12)–(16) divisor
charge and the two boundary amplitudes.  The companion file currently declares these out of scope;
that must be replaced once they are proved.

## Key reusable discoveries

- `GaloisForLFunctions.HTGeometry.QuantileCoupling` already contains `quantile`,
  `quantile_le_iff`, `measurable_quantile` and **`map_quantile_eq`** (inverse-transform sampling).
  mathlib has no probability-integral transform; this corpus module is the entry point.
- `MeasureTheory.lpBoundedMulCLM` (`HTGeometry/LpBoundedMultiplier.lean`) is the bounded
  multiplication operator; `KleinGordon*` modules have the ℝⁿ-Lebesgue-only versions of
  self-adjointness/dense range — the general-measure versions are now in
  `BoundedMultiplierHilbert`.
- `RHTower.unitIntervalMeasure = volume.restrict (Icc 0 1)`; the equality with
  `volume.restrict (Ioo 0 1)` is `RHTower.unitIntervalMeasure_eq` (new).
- Traps: `AEStronglyMeasurable.div` needs `ContinuousDiv`, absent for ℂ — use `mul` + `inv₀`.
  `field_simp` needs the `≠ 0` hypothesis in context.  Replacing `(M:ℂ)` by `√M·√M` via
  `rw [← hMM]` before `field_simp` is what makes the mass algebra close.
