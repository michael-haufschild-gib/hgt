# Formalization certificate: quantile-weighted universal Volterra boundary system

- **ID:** `hedenmalm-quantile-volterra-universal-boundary-defect-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `hedenmalm-quantile-volterra-universal-boundary-defect.md`

## Lean modules

```text
formal/GaloisForLFunctions/HTGeometry/WeightedDensityL2.lean
formal/GaloisForLFunctions/HTGeometry/PositiveDensityQuantile.lean
formal/GaloisForLFunctions/HTGeometry/BoundedMultiplierHilbert.lean
formal/GaloisForLFunctions/RHTower/HedenmalmPinnedVolterraBoundaryDefect.lean
formal/GaloisForLFunctions/RHTower/HedenmalmQuantileNormalForm.lean
formal/GaloisForLFunctions/RHTower/HedenmalmQuantileMetric.lean
```

All six are reachable from `GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`.

## Formal theorem chain

| # | card statement | Lean declaration |
|---|---|---|
| 0 | source class inhabited | `GaloisForLFunctions.HTGeometry.gaussianSource` |
| 0a | positive mass, probability law | `PositiveDensitySource.mass_pos`, `PositiveDensitySource.instIsProbabilityMeasureLaw` |
| 0b | `p` is `C1` with derivative `k/M` | `PositiveDensitySource.hasDerivAt_cdfFun` |
| 0c | `p` strictly increasing onto `(0,1)` | `PositiveDensitySource.strictMono_cdfFun`, `PositiveDensitySource.cdfFun_mem_Ioo`, `PositiveDensitySource.surjOn_cdfFun` |
| 0d | `Q` is the two-sided inverse of `p` | `PositiveDensitySource.quantile_cdfFun`, `PositiveDensitySource.cdfFun_quantile` |
| 0e | both transport laws | `PositiveDensitySource.measurePreserving_quantileFun`, `PositiveDensitySource.measurePreserving_cdfFun` |
| 0f | positive-density unitary | `GaloisForLFunctions.HTGeometry.weightedDensityUnitary` |
| `(1)` | `U` unitary `H_k -> L2(0,1)` | `RHTower.HedenmalmQuantile.quantileUnitary` |
| `(2)` | its pointwise formula | `RHTower.HedenmalmQuantile.quantileUnitary_ae` |
| — | `dx = q dt` change of variables | `RHTower.HedenmalmQuantile.integral_comp_quantile`, `RHTower.HedenmalmQuantile.setIntegral_comp_quantile` |
| — | source vectors are Lebesgue integrable | `RHTower.HedenmalmQuantile.integrable_sourceSpace` |
| — | `B f` at the quantile point | `RHTower.HedenmalmQuantile.sourceInverse_quantileFun` |
| `(3)` | `T = i M_q C`, explicit form | `RHTower.HedenmalmQuantile.quantileTransform_sourceInverse` |
| `(3)` | `T = i M_q C` against the universal `C` | `RHTower.HedenmalmQuantile.quantileTransform_sourceInverse_eq_pinned` |
| `(4)` | `G = M_(1/q)` bounded | `RHTower.HedenmalmQuantile.metricOperator`, `RHTower.HedenmalmQuantile.norm_metricOperator_le` |
| `(4)` | positive, injective, self-adjoint, dense range | `RHTower.HedenmalmQuantile.metricSymbol_pos`, `metricOperator_injective`, `metricOperator_inner`, `metricOperator_denseRange` |
| `(4)` | no positive lower bound | `RHTower.HedenmalmQuantile.not_boundedBelow_metricOperator` |
| `(4a)` | `<G U f, U f> = M^(-1) integral abs f squared` | `RHTower.HedenmalmQuantile.inner_metricOperator_quantileUnitary`, `RHTower.HedenmalmQuantile.quantileMetric_pullback` |
| `(5)` | `C* + C` affine, rank two, inertia `(1,1)` | `RHTower.pinnedBoundaryCLM_exact_rankTwo_mixed_inertia`, `RHTower.range_pinnedBoundaryCLM_eq_affineSubspace`, `RHTower.finrank_range_pinnedBoundaryCLM` |
| `(5a)` | bounded-composite local-metric rigidity | `RHTower.pointwiseMultiplier_anticommutator_eq_zero_imp_eq_zero` |
| `(5a)` | the composite coefficient is such a multiplier | `RHTower.HedenmalmQuantile.isPinnedPointwiseMultiplier_lpBoundedMulCLM`, `RHTower.HedenmalmQuantile.eq_zero_of_anticommutator` |
| — | no injective bounded symmetrizer | `RHTower.no_injective_pinnedVolterra_anticommutator` |

## Verification

```bash
cd formal
lake env lean GaloisForLFunctions/HTGeometry/WeightedDensityL2.lean
lake env lean GaloisForLFunctions/HTGeometry/PositiveDensityQuantile.lean
lake env lean GaloisForLFunctions/HTGeometry/BoundedMultiplierHilbert.lean
lake env lean GaloisForLFunctions/RHTower/HedenmalmQuantileNormalForm.lean
lake env lean GaloisForLFunctions/RHTower/HedenmalmQuantileMetric.lean
lake build GaloisForLFunctions.RHTower.HedenmalmQuantileMetric
```

All clean.  `#print axioms` on every declaration in the table reports only `propext`,
`Classical.choice` and `Quot.sound`.

## What is deliberately not formalized

The successor obligation --- a source law forcing every `Xi` root mode's quantile trace `(m,c)`
into the null cone `Re(c conj m) = 0` --- is open research, not formalization debt.  The card's
`(6)`--`(16)` are statements about root modes of the specific theta source and are consequences of
that open obligation together with the compressed-inverse card; they are not part of the
source-normal classification certified here.
