# Internal claim map

Paper text is presentation-layer mathematics and contains no formalization discussion. This file
is internal audit metadata.

- **Corpus snapshot:** `fc513fbbe1fe0b1d6461bf8b53a09f4099fdc4b4` plus explicitly listed
  working-tree additions checked directly on 2026-08-03.
- **External novelty:** not audited in this revision.
- **RH status:** no proof of RH is claimed. The closure theorem is an unconditional implication
  whose producer hypothesis is stated explicitly.

## Headline law

| Paper claim | Formal witness |
|---|---|
| factorization through attained range iff observation kernel pair refines target kernel pair | `HTGeometry/CompletionKernelPairTransversalityLaw.lean`: `factorsThroughRange_iff_kernelRefines` |
| heterogeneous family recovery iff factorization through joint record | same: `observationFamilyRecovers_iff_factorsThroughRecordRange` |
| serial postprocessing cannot restore lost target; injective transport is neutral | same: `not_factorsThroughRange_postprocess_of_not_factorsThroughRange`, `factorsThroughRange_comp_iff_of_injective` |
| parallel observation intersects invisible radicals | `HTGeometry/SourcePointedObservationNetworkLaw.lean`: `ker_pairedObservation`, `isConservativeOn_paired_iff` |
| reflection-invariant observation forces every factored odd charge to vanish | `HTGeometry/CompletionKernelPairTransversalityLaw.lean`: `target_eq_zero_of_reflectionParity_factorsThrough_invariantCompletion` |
| sufficient transverse channel separates every nonzero charged reflected pair | same: `transverseChannel_separates_reflection_of_oddCharge_ne_zero`, `reflectionOddPart_ne_zero_of_jointlyRecovers` |
| serial source-sector conservativity iff every stage is conservative on propagated sector | `HTGeometry/SourcePointedConservativityChainLaw.lean`: `isConservativeOn_comp_iff` |
| uniform lower bounds multiply along the chain | same: `isUniformlyConservativeOn_comp` |
| finite augmentation kernel is exactly anchored zero-sum boundary range | `HTGeometry/ResolvedSourceAugmentationConservativityLaw.lean`: `ker_finiteResolvedDefectAugmentation_eq_range_boundary` |

## Green and arithmetic source

| Paper claim | Formal witness |
|---|---|
| every observer uniquely splits into absolute orientation and relative Green transgression | `HTGeometry/GreenObservationSplittingLaw.lean`: `greenObservation_primary_add_secondary`, `greenObservation_primary_secondary_unique` |
| boundary-blind iff unique factorization through orientation trace | `HTGeometry/OrientationTraceFactorizationLaw.lean`: `orientationTrace_factorization_unique_iff`; also `greenObservation_traceFactorization_iff_secondary_eq_zero` |
| local and all-prime Calderón--Witt source instantiation | `RHTower/Deninger/DeningerCalderonWittOrientationTransgressionCompleteness.lean`: local/global `...OrientationTransgressionCompleteness` and primary/secondary theorems |
| paper-level conjunction with completed source law | `RHTower/RiemannOrientationTransgressionPaperCertificate.lean`: `riemannOrientationTransgressionPaperCore` |

## Completion boundary

| Paper claim | Formal witness |
|---|---|
| proper closed bi-dense subspace iff both injective dense-range Hilbert legs fail lower bounds | `RHTower/PreQuasiGelfandTwoSidedSingularDefect.lean`: `twoSidedSingular_iff_hasProperClosedBiDenseSubspace` |
| codimension-one construction | same: `exists_biDense_hyperplane_of_twoSidedSingular` |
| complete source finite-depth injectivity | `RHTower/CompleteResolutionSourceEmbeddingReflectionLaw.lean`: `completeResolutionSourceEmbedding_injective` |
| cofinal source collapse and inverse conditioning | `RHTower/CompleteResolutionCofinalConditioningLaw.lean`: `tendsto_completeResolutionSourceVector_pointSection`, `tendsto_inv_norm_completeResolutionSourceVector_sub_atTop`, `completeResolution_cofinalConservationSingularity_law` |
| no uniformly Lipschitz cofinal observer can retain fixed separation | same: `no_uniformLipschitz_completeResolutionObserver_fixedSeparation` |
| finite-coordinate surjectivity makes product-topology relation maximally vertical | same: `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod` and supporting finite-projection/density theorems |
| informative completion topology is strictly finer than product topology | same: `completeResolution_countablePrime_informative_forces_strictTopology` |
| reflection sewing norm is beyond every finite Wold--Rees order | `RHTower/PrimeValuationHellingerReesReflectionFracture.lean`: `reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder` |
| combined nonlocal--singular Riemann-source law | `RHTower/RiemannSourceNonlocalSingularCompletionLaw.lean`: `riemannSource_nonlocalSingularCompletion_law`, `xiRight_orientedNonlocalSingularCompletion_law` |

## Orientation, jets, and analytic shadows

| Paper claim | Formal witness |
|---|---|
| exchanged idempotent orientation is a commutator and cyclic traces kill it | `RHTower/RealCoronaQuaternionicCyclic.lean`: `realCoronaOrientation_eq_commutator`, `realCoronaOrientation_trace_eq_zero` |
| explicit graded two-dimensional trace detects orientation | same: `gradedMatrixTrace_realCoronaMatrixGrading_self` |
| coherent infinite jets split into position and based Maurer--Cartan data, including constant-subgroup quotient | `HTGeometry/AlgebraicGroupInfiniteJet.lean`: `algebraicInfiniteJetMaurerCartanTrivialization`, `algebraicInfiniteJetQuotientConstantsEquivBased`, `algebraicInfiniteJetQuotientConstantSubgroupEquivPositionVelocity` |
| formally étale finite-jet compatibility | `HTGeometry/FormalEtaleJetCompatibility.lean`: `formallyEtale_truncatedArc_pullback_bijective` (working-tree addition, direct check passed) |
| exponent-one canonical product equals reciprocal Gamma gauge | `HTGeometry/GammaWeierstrassCanonicalProduct.lean`: `powerCanonicalProduct_one_eq` |
| exponent-one and reciprocal-natural exponents are hypertranscendental | `HTGeometry/OnePowerCanonicalProductHypertranscendence.lean`: `hypertranscendental_powerCanonicalProduct_one`, `hypertranscendental_powerCanonicalProduct_inv_nat` |
| every positive even exponent is differentially algebraic via sine factorization | `HTGeometry/EvenPowerCanonicalProductDA.lean`: `powerCanonicalProduct_even_eq_prod_sinc`, `differentiallyAlgebraic_powerCanonicalProduct_of_even` |
| exact root-of-unity cyclic norm | `HTGeometry/RationalPowerCyclicNorm.lean`: `prod_powerCanonicalProduct_primitiveRoot` |
| Bohr hull closed embedding and power-faithful phase recovery | `HTGeometry/BohrHullContinuity.lean`: `isClosedEmbedding_bohrHullMap`; `HTGeometry/BohrPowerBoundary.lean`: `cexpSeriesCarrier_phase_injective_pow` |
| ordered pulse tomography for common-domain unbounded generators | `HTGeometry/ChronometricRegularPulseTomography.lean`: `nestedRealDerivAtZero_orderedPulseApply`; `HTGeometry/ChronometricUnboundedPulseModel.lean`: `natGenerator_unbounded`, `exists_unbounded_regularPulseFamily` |
| Airy first-deviation sign and zero-loop rigidity | `HTGeometry/AiryTowerStokesRigidity.lean`: `diagonalLoop_neg_of_first_lt`, `diagonalLoop_pos_of_first_gt`, `diagonalLoop_eq_zero_iff_isAiryTower` |
| balanced Xi Green connection carries unsquared outer charge | `RHTower/XiSourceBoundaryOrientationConservation.lean`: `xiDepthNearby_sourceBoundaryOrientationConservation` |

## Excluded from claims

- No assertion that the polarized conservativity law is externally novel.
- No assertion that every RH proof must use Hilbert completion.
- No assertion that the five conditions in the Riemann closure theorem have been jointly produced.
- No assertion that cyclic trace failure rules out noncyclic, vector-valued, differential, Stokes,
  or cohomological routes.
