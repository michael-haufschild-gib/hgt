# Hedenmalm folder → stage 3: progress log (started 2026-08-07)

Task: formalize unconditionally in Lean every proven statement in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/` (9 cards), then move each
card to `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.

## CARD 1 of 9 — DONE and MOVED: `hedenmalm-quantile-volterra-universal-boundary-defect`

Every numbered statement `(1)`–`(16)` is now a Lean theorem.  Nine modules, all wired into the
`HTGeometry`/`RHTower` umbrellas, all `#print axioms` clean.

New reusable infrastructure (HTGeometry):
- `WeightedDensityL2.lean` — `weightedDensityUnitary : L²(μ.withDensity w) ≃ₗᵢ L²(μ)`, `f ↦ √w f`.
- `PositiveDensityQuantile.lean` — `structure PositiveDensitySource` (k continuous/positive/
  integrable) with `mass`, `normalized`, `law`, `cdfFun`, `quantileFun`; `p` is C¹ with derivative
  `k/M`, strictly mono onto `(0,1)`, `Q` two-sided inverse, both transport laws, `integrable_law_iff`,
  `integrableOn_comp_quantileFun_iff`, witness `gaussianSource`.
- `BoundedMultiplierHilbert.lean` — measure-agnostic self-adjoint/injective/dense-range for
  `lpBoundedMulCLM`.

New RHTower modules: `HedenmalmQuantileNormalForm` (U unitary, `T = i M_q C`),
`HedenmalmQuantileMetric` (G bounded/injective/self-adjoint/dense/no lower bound, (4a)),
`HedenmalmQuantileBoundaryFlux` ((6),(7),(8),(15),(16), ±1/√12 eigenvalues),
`HedenmalmQuantileRootMode` (Q' = q, `xiC`, (9),(10),(11)),
`HedenmalmQuantileDivisorCharge` ((12),(13),(14)).

Two named hypotheses are used and documented in the companion: `HasShiftedTail S z` (convergence of
`Xi_C` at z) and `RootModeEndpoints S z` (endpoint vanishing of the mode energy).  Both are exactly
what the card's own proof assumes; two-point versions of the same theorems hold with no endpoint
input.

## REMAINING 8 CARDS and their Lean state

| card | Lean at start | main missing machinery |
|---|---|---|
| `hedenmalm-theta-source-compressed-inverse-determinant` | `HTGeometry.SourceGrushinInverse` only | Hilbert–Schmidt operators with kernels, regularized determinant `det₂`, Hadamard product |
| `hedenmalm-supersymmetric-fredholm-range-divisor` | **none** (`[OPEN]`) | unbounded weighted first-order operators, Fredholm index, Witten square |
| `hedenmalm-essential-inverse-flow-prime-tomography` | none | punctured Riesz trace, von Mangoldt weld |
| `hedenmalm-prime-translation-rank-one-anomaly` | none | rank-one commutator, Jordan blocks |
| `hedenmalm-two-prime-theta-interval-normal-frame` | none | sinc multipliers, no-common-zero |
| `hedenmalm-pair-weil-polarization-law` | large | one open gate: Guinand–Weil closed form |
| `hedenmalm-reflection-folded-dirac-source-defect` | large | audit gates |
| `hedenmalm-theta-flat-borel-holonomy-law` | large | `[OPEN CORE: THETA_BOREL_REFLECTED_COMMON_DOMAIN]` |

## Key reusable discoveries

- `HTGeometry.QuantileCoupling` already has `quantile`, `quantile_le_iff`, `measurable_quantile`,
  **`map_quantile_eq`** (inverse-transform sampling).  mathlib has no probability-integral transform.
- `MeasureTheory.lpBoundedMulCLM` (`HTGeometry/LpBoundedMultiplier.lean`) is the bounded
  multiplication operator; `KleinGordon*` has only the ℝⁿ-Lebesgue versions of self-adjointness and
  dense range — general-measure versions now in `BoundedMultiplierHilbert`.
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder` gives residues of
  logarithmic derivatives — the input for divisor-charge statements.
- `RHTower.unitIntervalMeasure = volume.restrict (Icc 0 1)`; equality with `restrict (Ioo 0 1)` is
  `RHTower.unitIntervalMeasure_eq`.

## Lean traps hit (v4.32)

- `AEStronglyMeasurable.div` needs `ContinuousDiv`, absent for ℂ — use `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis *in the context*.
- Replacing `(M:ℂ)` by `√M*√M` via `rw [← hMM]` before `field_simp` is what closes mass algebra.
- `Complex.reCLM.hasFDerivAt.comp_hasDerivAt` fails on instance paths for ℝ-valued targets; work in
  ℂ with `HasDerivAt.star` and `conj w * w = ((‖w‖^2 : ℝ) : ℂ)` instead.
- `star` vs `starRingEnd ℂ`: they are defeq, so `show` converts, but `rw` will not.
- `Integrable.star` does not exist; build conj-integrability from `⟨conj∘f measurable, h.2.congr'⟩`.
