# Hedenmalm folder → stage 3: progress log (2026-08-07)

Task: formalize unconditionally in Lean every proven statement in the 9 cards of
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/hedenmalm/`, then `git mv` each to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/` with an
`<id>-formalized.md` companion.  **NOT FINISHED — 3 of 9 moved.**

## DONE — 3 of 9 in stage 3

1. **`hedenmalm-quantile-volterra-universal-boundary-defect`** — every numbered statement
   `(1)`–`(16)` newly formalized in 9 modules (see companion for the full table):
   `HTGeometry/WeightedDensityL2.lean`, `HTGeometry/PositiveDensityQuantile.lean`,
   `HTGeometry/BoundedMultiplierHilbert.lean`, `RHTower/HedenmalmQuantileNormalForm.lean`,
   `RHTower/HedenmalmQuantileMetric.lean`, `RHTower/HedenmalmQuantileBoundaryFlux.lean`,
   `RHTower/HedenmalmQuantileRootMode.lean`, `RHTower/HedenmalmQuantileDivisorCharge.lean`
   (+ the pre-existing `HedenmalmPinnedVolterraBoundaryDefect`).
2. **`hedenmalm-reflection-folded-dirac-source-defect`** — was already fully formalized; audited
   (all names resolve, 20 `#print axioms` clean) and moved.
3. **`hedenmalm-theta-flat-borel-holonomy-law`** — was already fully formalized; audited (51/53
   backticked names resolve; the 2 exceptions are an open-core marker and a math symbol; 12 axioms
   clean) and moved.

## IN PROGRESS — card 4: `hedenmalm-prime-translation-rank-one-anomaly`

New module `RHTower/HedenmalmPrimeTranslationAnomaly.lean` (compiles, wired, axiom-clean) proves:
- `setIntegral_Iic_comp_sub` / `_add` — translation of half-line integrals;
- `sourceFunctional_sourceShift`, `sourceFunctional_integerShift`;
- **`sourceInverse_sourceShift`** = card `(7)`, the rank-one real-translation commutator;
- **`sourceInverse_integerShift`** = card `(8)`, the normalized-integer version;
- `sourceChar_sub`, **`sourceEvaluation_integerShift`** = card `(10)`, the literal Dirichlet
  character `n^{-s(z)}` with `dirichletExponent z = 1/2 + i z`.

STILL TO DO on that card: `r_a ≠ 0` / `r_n ≠ 0` (no nonzero real period), the explicit right mode
`(11)`–`(12)`, the integer Mellin expansion `(14)` (needs the theta series), reflection package
`(15)`, `dim ker = 1` `(16)`, and the jet law `(17)`–`(18)` (binomial; easy once the jets are
defined by the integral formula).

## REMAINING 5 further CARDS

| card | Lean state | missing machinery |
|---|---|---|
| `hedenmalm-pair-weil-polarization-law` | large | ONE gate: extend the prime+Gamma equality from the Cauchy/resolvent core to the **full Guinand–Weil test algebra in closed form**.  Existing: `XiWeilPolarization`, `XiWeilResolventSource`, `XiWeilHilbertCore`, `XiQuotientRealDecay`, `XiHorizontalStripDecay`, `primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace` |
| `hedenmalm-theta-source-compressed-inverse-determinant` | `HTGeometry.SourceGrushinInverse` only | Hilbert–Schmidt integral operators, regularized determinant `det₂`, genus-one Hadamard product |
| `hedenmalm-supersymmetric-fredholm-range-divisor` | **none** | unbounded weighted first-order operator, closed range, Fredholm index, Witten square |
| `hedenmalm-essential-inverse-flow-prime-tomography` | none | punctured Riesz trace, essential inverse flow, von Mangoldt weld |
| `hedenmalm-two-prime-theta-interval-normal-frame` | none | sinc multipliers for `log 2`/`log 3`, no common zero, frame obstruction |

## Key reusable infrastructure now available

- `PositiveDensitySource` (k continuous/positive/integrable) with mass, normalized law, `cdfFun`
  (C¹, derivative `k/M`, strictly mono onto `(0,1)`), `quantileFun` (two-sided inverse,
  `hasDerivAt_quantileFun` gives `Q' = q`), both measure-transport laws, `integrable_law_iff`,
  `integrableOn_comp_quantileFun_iff`, witness `gaussianSource`.
- `weightedDensityUnitary : L²(μ.withDensity w) ≃ₗᵢ L²(μ)`.
- `HedenmalmQuantile.sourceInverse` = the explicit Hedenmalm inverse `B`;
  `HedenmalmQuantile.sourceChar z x = exp(i z x)`; `HedenmalmQuantile.xiC`.
- General-measure self-adjointness/injectivity/dense-range for `lpBoundedMulCLM`
  (`BoundedMultiplierHilbert`).
- `HTGeometry.QuantileCoupling.map_quantile_eq` (inverse-transform sampling; mathlib has none).
- `HTGeometry.LogarithmicResidueQuantization.logDeriv_residue_of_meromorphicOrder`.

## Lean traps hit (v4.32)

- `AEStronglyMeasurable.div` needs `ContinuousDiv`, absent for ℂ — use `mul` + `Continuous.inv₀`.
- `field_simp` needs the `≠ 0` hypothesis in the local context; substituting `(M:ℂ) = √M*√M` before
  `field_simp` is what closes the mass algebra.
- `Complex.reCLM.hasFDerivAt.comp_hasDerivAt` fails on ℝ-target instance paths; stay in ℂ with
  `HasDerivAt.star` and `conj w * w = ((‖w‖^2 : ℝ) : ℂ)`.
- `star` vs `starRingEnd ℂ` are defeq: `show` converts, `rw` does not.
- `Integrable.star` does not exist; build it as `⟨conj∘f measurable, h.2.congr'⟩`.
- `Set.uIcc_subset_Ioo` does not exist; use `Set.ordConnected_Ioo.uIcc_subset`.
- `rw [someDef]` fails for defs applied to arguments — use `show` (defeq) instead.
- `integral_add_right_eq_self` needs `(μ := volume)` or the instance search gets stuck.
- Bash cwd persists between calls: `cd formal` once; after any `cd` to the repo root, greps against
  `GaloisForLFunctions/...` silently return nothing.
- `scripts/formal_tools.py lint` currently reports 4 pre-existing unreachable RHTower modules
  (`ConstrainedProlateSpectralIdentification`, `ProlateFourierSignSectors`,
  `RouteRSquarefullStokesSummabilityProducer`, `SlepianKernelScaledFubini`) — not from this work.
  Another agent was editing `HTGeometry.lean` concurrently.
