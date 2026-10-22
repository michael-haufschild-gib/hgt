# Claim audit: Relation-kernel transgression and the Riemann boundary

Paper prose does not mention formalization. This file is internal audit only.

## Central universal theorem

| Paper claim | Formal theorem(s) | Status |
|---|---|---|
| Pullback primitive restricts to a homomorphism on the quotient relation kernel | `DeningerNormalizedCocycle.primitive_mul_of_mem_ker`, `DeningerNormalizedCocycle.kernelTransgression` | Proved |
| Kernel character is independent of primitive under degree-one descent | `DeningerNormalizedCocycle.primitiveDifference`, `DeningerNormalizedCocycle.kernelTransgression_apply_eq_of_degreeOneDescent` | Proved |
| Kernel character vanishes iff cocycle is a coboundary downstairs | `DeningerNormalizedCocycle.kernelTransgression_eq_one_iff_isCoboundary` | Proved |
| Alternating rational cocycle is a coboundary iff it is zero | `DeningerNormalizedCocycle.isCoboundary_iff_eq_zero_of_alternating` | Proved |
| Baumslag free-rational cover supplies primitive and canonical vanishing criterion | `deningerBauFree_exists_canonical_kernelTransgression`, `DeningerNormalizedCocycle.deningerBauFree_exists_alternating_kernelTransgression` | Proved |

Formal source: `formal/GaloisForLFunctions/RHTower/Deninger/DeningerRelationKernelTransgression.lean`.

## Actual arithmetic calibrator

| Paper claim | Formal theorem(s) | Status |
|---|---|---|
| Calderón–Witt cup is alternating | `deningerCalderonWittCup_skew`, `deningerCalderonWittCup_self`, `deningerCalderonWittCupCocycle_alternating` | Proved |
| Local vector-valued cup has zero left radical | `deningerCalderonWittCup_leftRadical_eq_zero` | Proved |
| Cup is preserved under finite gauge-corrected refinement | `deningerCalderonWittFiniteStageCup_refinement` | Proved |
| All-prime finite-support source retains local cups componentwise | `deningerCalderonWittGlobalCup_lof_same`, `deningerCalderonWittGlobalCup_component` | Proved |
| Actual local cocycle is nonzero | `deningerCalderonWittCupCocycle_ne_zero` | Proved |
| A free-rational primitive has nonzero relation-kernel restriction | `exists_deningerCalderonWitt_nonzero_relationKernelTransgression` | Proved |

Sources:

- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCalderonWittDerivedCupSource.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerRelationKernelTransgression.lean`

## Completed source and Green transport

| Paper claim | Formal theorem(s) | Status |
|---|---|---|
| Literal two-line prime–Gamma Cauchy boundary is Bochner integrable | `integrable_reflectedGaussianPrimeGammaCauchyBoundary` | Proved |
| Its integral is the fixed reflected Gaussian horizon | `integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2` | Proved |
| Completed harmonic multiplier is physical `i sign(D)` and squares to `-I` | `deningerXiHarmonicHodge_eq_deningerHodgeW`, `deningerXiHarmonicHodge_sq` | Proved |
| Unique completed Green primitive is harmonic Hodge of fixed source | `reflectedGaussianHorizonCompletedGreenPrimitive_eq_harmonicHodge` | Proved |
| Oriented Cauchy boundary integrates to completed Green primitive | `integral_reflectedGaussianPrimeGammaOrientedCauchyBoundary_eq_greenPrimitive` | Proved |
| Completed Green operator is unique extension of finite-jet Green reflection | `deningerArithmeticCompletedSourceGreen_unique`, `deningerArithmeticCompletedSourceGreen_extends_compact` | Proved |
| Adaptive columns converge to same primitive and detector | `tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn`, `tendsto_reflectedGaussianAdaptiveHarmonicGreenPrimitiveColumn_eq_orientedCauchyBoundary`, `tendsto_adaptivePrimeNormalInfiniteDepthGreenFractureColumn_eq_cauchyBoundary` | Proved |

Sources:

- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianPrimeGammaCauchyLanding.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianCompletedSourceGreen.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianHarmonicSourcePrimitive.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerAdaptiveHarmonicGreenBoundary.lean`

## Completion wall and retained defect

| Paper claim | Formal theorem(s) | Status |
|---|---|---|
| Compact source Green range equals finite-jet range | `deningerArithmeticSourceGreen_range_eq_finiteJetHilbert_range` | Proved |
| Fixed Gaussian horizon is outside compact Green range but in its closure | `reflectedGaussianHorizonAdmittedResidue_not_mem_sourceGreen_range`, `reflectedGaussianHorizonAdmittedResidue_mem_closure_sourceGreen_range` | Proved |
| Horizontal fracture is exactly `2(Re ρ - 1/2)` | `xiNearbyPoleDualityAdjunctionFracture_eq_two_re` | Proved |
| Fixed Green provenance vanishes iff RH | `reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis` | Proved equivalence, not RH |
| Completed resolved defect is antidiagonal and codiagonal zero | `deningerArithmeticCompletedGreenResolvedDefect_codiagonal` plus definition `deningerArithmeticCompletedGreenResolvedDefect` | Proved |
| Resolved source defect vanishes iff RH | `deningerArithmeticGreenResolvedDefect_eq_zero_iff_riemannHypothesis` | Proved equivalence, not RH |
| Resolved provenance quotient class vanishes iff RH | `reflectedGaussianHorizonGreenResolvedClass_eq_zero_iff_riemannHypothesis` | Proved equivalence, not RH |
| Off-axis coface quotient retains provenance; zero phase retains diagonal with zero provenance | `hellingerGammaResolvedProvenanceQuotientProjection_injective_of_ne`, `hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_zero` | Proved |
| Balanced primitive range cannot contain nonzero codiagonal-kernel defect | `hellingerGammaCompletedBalancedPrimitive_range_disjoint_codiagonalKernel` | Proved |

Sources:

- `formal/GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianGreenRangeWall.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerReflectedGaussianCompletedGreenDefect.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerGreenResolvedSourceConservativityCriterion.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerCompletedXiHellingerGammaResolvedProvenanceSaturation.lean`
- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerResolvedDefectHellingerGammaBalancedCofaceNoGo.lean`

## Literal boundary regulator and Ward comparison

| Paper claim | Formal theorem(s) | Status |
|---|---|---|
| Secondary source restriction annihilates every literal Meyer–Poisson boundary | `deningerMeyerPoissonBoundary_secondaryValue_zero`, `deningerMeyerPoissonBoundary_secondaryRestriction_zero` | Proved on stated radial two-collar domain |
| Secondary Green energy has exact reflected-prime-graph radical | `deningerMeyerSecondarySchwartzGreenEnergy_eq_zero_iff` | Proved |
| Unweighted Ward energy is either RH/zero or non-RH/strictly above `8π` | `xiWardEdgeQuadEnergy_arithmeticPhaseClassification` | Proved classification, not RH |
| Endpoint-weighted Ward index is below `93π/1000` and vanishes iff RH | `xiEndpointWeightedWardIndex_lt_ninetyThreePi_over_thousand`, `xiEndpointWeightedWardIndex_eq_zero_iff_rh` | Proved; different weighting from unweighted Ward energy |

Sources:

- `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerSecondaryPoissonRegulator.lean`
- `formal/GaloisForLFunctions/RHTower/XiWardEdgeEnergyPhaseQuantizationUniversalityLaw.lean`
- `formal/GaloisForLFunctions/RHTower/XiWardEndpointSourceIndex.lean`

## Deliberately open claim

The following statement has **no formal theorem and is not claimed as proved in the paper**:

```text
Trans(completed Green provenance at ρ) = D_ρ · τ_p,
with the compared representative killed by the literal Meyer–Poisson boundary regulator.
```

Paper labels this the arithmetic comparison theorem and proves only the conditional implication:
comparison theorem ⇒ every `D_ρ = 0` ⇒ RH.

No theorem currently identifies the prime–Gamma Cauchy/Green provenance chain with the Baumslag relation-kernel transgression while preserving the unsquared coefficient. This is sole load-bearing open bridge in paper route.

