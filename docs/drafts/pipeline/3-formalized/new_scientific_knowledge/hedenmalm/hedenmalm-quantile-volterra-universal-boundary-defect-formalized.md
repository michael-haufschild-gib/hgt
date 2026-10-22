# Formalization certificate: quantile-weighted universal Volterra boundary system

- **ID:** `hedenmalm-quantile-volterra-universal-boundary-defect-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `hedenmalm-quantile-volterra-universal-boundary-defect.md`

## Lean modules

```text
formal/GaloisForLFunctions/HTGeometry/WeightedDensityL2.lean
formal/GaloisForLFunctions/HTGeometry/PositiveDensityQuantile.lean
formal/GaloisForLFunctions/HTGeometry/BoundedMultiplierHilbert.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmPinnedVolterraBoundaryDefect.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileNormalForm.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileMetric.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileBoundaryFlux.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileRootMode.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileDivisorCharge.lean
```

All nine are reachable from `GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`.

## Formal theorem chain

Namespace `RHTower.HedenmalmQuantile` unless stated otherwise.

| # | card statement | Lean declaration |
|---|---|---|
| 0 | source class inhabited | `GaloisForLFunctions.HTGeometry.gaussianSource` |
| 0a | positive mass, probability law | `PositiveDensitySource.mass_pos`, `PositiveDensitySource.instIsProbabilityMeasureLaw` |
| 0b | `p` is `C1` with derivative `k/M` | `PositiveDensitySource.hasDerivAt_cdfFun` |
| 0c | `p` strictly increasing onto `(0,1)` | `PositiveDensitySource.strictMono_cdfFun`, `PositiveDensitySource.cdfFun_mem_Ioo`, `PositiveDensitySource.surjOn_cdfFun` |
| 0d | `Q` is the two-sided inverse of `p` | `PositiveDensitySource.quantile_cdfFun`, `PositiveDensitySource.cdfFun_quantile` |
| 0e | both transport laws | `PositiveDensitySource.measurePreserving_quantileFun`, `PositiveDensitySource.measurePreserving_cdfFun` |
| 0f | positive-density unitary | `GaloisForLFunctions.HTGeometry.weightedDensityUnitary` |
| 0g | `Q' = q` | `hasDerivAt_quantileFun`, `continuousOn_quantileFun` |
| `(1)` | `U` unitary `H_k -> L2(0,1)` | `quantileUnitary` |
| `(2)` | its pointwise formula | `quantileUnitary_ae` |
| — | `dx = q dt` change of variables | `integral_comp_quantile`, `setIntegral_comp_quantile` |
| — | source vectors are Lebesgue integrable | `integrable_sourceSpace` |
| — | `B f` at the quantile point | `sourceInverse_quantileFun` |
| `(3)` | `T = i M_q C`, explicit form | `quantileTransform_sourceInverse` |
| `(3)` | `T = i M_q C` against the universal `C` | `quantileTransform_sourceInverse_eq_pinned` |
| `(4)` | `G = M_(1/q)` bounded | `metricOperator`, `norm_metricOperator_le` |
| `(4)` | positive, injective, self-adjoint, dense range | `metricSymbol_pos`, `metricOperator_injective`, `metricOperator_inner`, `metricOperator_denseRange` |
| `(4)` | no positive lower bound | `not_boundedBelow_metricOperator`, `exists_norm_metricSymbol_lt` |
| `(4a)` | `<G U f, U f> = M^(-1) integral abs f squared` | `inner_metricOperator_quantileUnitary`, `quantileMetric_pullback` |
| `(5)` | `C* + C` affine, rank two, inertia `(1,1)` | `RHTower.pinnedBoundaryCLM_exact_rankTwo_mixed_inertia`, `RHTower.range_pinnedBoundaryCLM_eq_affineSubspace`, `RHTower.finrank_range_pinnedBoundaryCLM` |
| `(5)` | the two nonzero eigenvalues are `± 1/sqrt 12` | `RHTower.pinnedBoundaryCLM_pinnedFluxPositive`, `RHTower.pinnedBoundaryCLM_pinnedFluxNegative` |
| `(5a)` | bounded-composite local-metric rigidity | `RHTower.pointwiseMultiplier_anticommutator_eq_zero_imp_eq_zero` |
| `(5a)` | the composite coefficient is such a multiplier | `isPinnedPointwiseMultiplier_lpBoundedMulCLM`, `eq_zero_of_anticommutator` |
| `(6)` | kernel is the codimension-two moment space | `RHTower.pinnedBoundaryCLM_eq_zero_iff` |
| `(7)` | `<R2 g,g> = -2 Re(c conj m)` | `RHTower.inner_pinnedBoundaryCLM_eq` |
| `(8)` | `2 Im(lambda) <G g,g> = <R2 g,g>` | `inner_pinnedBoundaryCLM_rootMode` |
| `(9)` | explicit root mode `h`, `g` | `rootH`, `rootG`, `rootMode_relation`, `hasDerivAt_rootH`, `rootH_zero` |
| `(9)` | uniqueness of the solution | `rootODE_two_point` |
| `(10)` | `integral exp(i z Q) = M^(-1) Xi_C(z)`, endpoint criterion | `integral_sourceChar_comp_quantile`, `rootA_one`, `rootA_one_eq_zero_iff` |
| `(11)` | ordered-correlation flux identity | `rootEnergy_two_point`, `rootFlux_identity`, `neg_rootH_eq_orderedCorrelation` |
| `(12)` | centered logarithmic residue is the charge | `centeredLogDeriv_residue`, `re_centeredLogDeriv_residue` |
| `(13)`/`(14)` | flux equals the modular divisor charge | `im_spectralValue_mul`, `inner_pinnedBoundaryCLM_divisorCharge` |
| `(15)` | the two boundary amplitudes | `RHTower.pinnedInAmplitude`, `RHTower.pinnedOutAmplitude` |
| `(16)` | `<R2 g,g> = abs a_in squared - abs a_out squared` | `RHTower.inner_pinnedBoundaryCLM_eq_amplitudes`, `inner_pinnedBoundaryCLM_eq_zero_iff_amplitudes` |
| — | no injective bounded symmetrizer | `RHTower.no_injective_pinnedVolterra_anticommutator` |

## The two analytic inputs are theorems, not hypotheses

Over the general positive-density class two analytic inputs appear as named hypotheses:

- `HasShiftedTail S z`: integrability of `k(x) e^{-Im(z) x}`, exactly the convergence of `Xi_C`
  at `z`, which makes `A(t) = integral of exp(i z Q)` a locally absolutely continuous primitive.
- `RootModeEndpoints S z`: integrability of the mode energy and of the mode, together with the
  vanishing of the mode energy at both endpoints.

**Both are discharged at the actual arithmetic source.**  `formal/GaloisForLFunctions/RHTower/`
supplies the instance `HedenmalmThetaSource.thetaSource` and

| input | discharged by |
|---|---|
| `HasShiftedTail thetaSource z` for `abs (Im z) < 1` | `HedenmalmThetaSourceUnconditional.hasShiftedTail_thetaSource` |
| `xiC thetaSource = XiC` on that strip | `HedenmalmThetaSourceUnconditional.xiC_thetaSource` |
| two-sided decay of the source mode at a zero | `HedenmalmThetaRootModeDecay.norm_sourceModeU_le` |
| `rootA` is the source primitive in quantile coordinates | `HedenmalmThetaRootEndpoints.rootA_eq_sourceModeI`, `rootH_eq_sourceModeU`, `norm_rootH_eq` |
| the two quantile boundary limits | `tendsto_quantileFun_nhdsGT_zero`, `tendsto_quantileFun_nhdsLT_one` |
| `RootModeEndpoints thetaSource z` for `abs (Im z) < 1` and `XiC z = 0` | `HedenmalmThetaRootEndpoints.rootModeEndpoints_thetaSource` |

so `(11)` holds for the Riemann source with no hypothesis on the source at all:

```text
rootFlux_identity_thetaSource
  : abs (Im z) < 1 -> XiC z = 0 ->
    (integral over (0,1) of -h)  .re  =  -(Im z) * integral over (0,1) of q * norm h squared
```

`XiC z = 0` is not a convenience: without it the mode does **not** vanish at `t -> 1` when
`Im z > 0`, so the endpoint bundle is false off the divisor.  This is exactly how the card uses
the identity.

Without those inputs the corresponding statements are still available in exact two-point form:
`rootODE_two_point` and `rootEnergy_two_point` hold between any two interior points with no
endpoint input at all.

## Verification

```bash
cd formal
lake env lean GaloisForLFunctions/HTGeometry/WeightedDensityL2.lean
lake env lean GaloisForLFunctions/HTGeometry/PositiveDensityQuantile.lean
lake env lean GaloisForLFunctions/HTGeometry/BoundedMultiplierHilbert.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileNormalForm.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileMetric.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileBoundaryFlux.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileRootMode.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmQuantileDivisorCharge.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileDivisorCharge
```

All clean.  `#print axioms` on every declaration in the table reports only `propext`,
`Classical.choice` and `Quot.sound`.
