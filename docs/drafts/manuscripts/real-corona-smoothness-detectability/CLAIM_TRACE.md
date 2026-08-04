# Claim trace

Paper: Smoothness--detectability conservation for Real-corona orientations

Scope rule: every mathematical result introduced by paper maps to an unconditional Lean
declaration. Historical context is cited, not used as an untracked premise. Stable facade:
GaloisForLFunctions.RHTower.RealCoronaFourProblemsResolution.

## Main results

| Paper claim | Facade declaration |
|---|---|
| Theorem 1.1, exhaustive fixed/free orbit-algebra law | realCoronaC2AtomicOrbitAlgebraLaw |
| Theorem 1.2, smoothness--detectability conservation | realCorona_smoothnessDetectabilityConservation |
| Theorem 1.3, odd complete-divisor zeta no-go | realCoronaP1_oddCompleteDivisor_zetaNoGo |
| Theorem 1.4, closed CCM Lefschetz is not anti-Real | realCoronaP2_lefschetz_not_antiReal |
| Theorem 1.4, scalar parity classification | realCoronaP2_scalarShift_antiReal_iff_star_eq_neg |
| Theorem 1.4, no anti-Real bivariant realization equals Lefschetz | realCoronaP2_no_bivariantChernRealization_eq_lefschetz |
| Theorem 1.4, exact Clifford survivor iL | realCoronaP2_cliffordTransgression_eq_i_lefschetz |
| Theorem 1.5, complete-strip smoothness no-go | realCoronaP3_completeStrip_not_smooth |
| Theorem 1.5, certified positive-degree no-go | realCoronaP3_positiveDegreeCompletion_not_smooth |
| Theorem 1.5, actual Xi case | realCoronaP3_riemannXi_not_smooth |
| Theorem 1.5, primitive self-dual Dirichlet cases | realCoronaP3_selfDualPrimitiveDirichlet_not_smooth |
| Theorem 1.5, completed-zeta powers smooth iff degree zero | realCoronaP3_xiPower_smooth_iff_degree_zero |
| Theorem 1.6, fixed-sector variation | realCoronaP4_fixedSectorVariation |
| Theorem 1.6, analytic-rank/K0/excess variation | realCoronaP4_analyticRankVariation_eq_kZero_add_excess |
| Theorem 1.6, concrete polynomial defect/rank | realCoronaP4_polynomialFamily_defectRank; realCoronaP4_polynomialFamily_centralKZeroRank |
| Theorem 1.6, fixed crossed-product K0 comparison | realCoronaP4_fixedCrossedProductKZero_comparison |
| Theorem 1.6, concrete signed variation | realCoronaP4_polynomialFamily_defectVariation |

## Section 2: universal orbit and invariant-domain law

| Paper identity/result | Lean declaration | Module |
|---|---|---|
| every involution orbit fixed or free | involution_orbit_fixed_or_free | RealCoronaC2OrbitConservationLaw.lean |
| free crossed product is M2(C) | freeReflectionMatrixRingEquiv | RealCoronaFreeCrossedProductMatrix.lean |
| explicit free inverse transform | freeReflectionMatrixInvFun_leftInverse; freeReflectionMatrixInvFun_rightInverse | same |
| free orientation maps to sign grading | freeReflectionMatrixRingEquiv_orientation | same |
| entrywise orientation commutator | freeOrbitOrientationMatrix_commutator_entry | same |
| fixed crossed product is two Fourier blocks | fixedReflectionFourierRingEquiv | RealCoronaFixedCrossedProductKZero.lean |
| explicit fixed inverse transform | fixedReflectionFourierInvFun_leftInverse; fixedReflectionFourierInvFun_rightInverse | same |
| fixed coefficient inclusion is diagonal | fixedReflectionFourierRingEquiv_coefficient | same |
| induced finite-coordinate K0 map is diagonal | fixedCoordinateToReflectionCrossedProductKZero | same |
| bundled exhaustive atomic law | c2AtomicOrbitAlgebraLaw | RealCoronaC2OrbitConservationLaw.lean |
| free/fixed orientation square defect | RealOrbitIdempotentDecomposition.orientation_sq | RealCoronaUniversalTransgression.lean |
| ordinary trace kills free orientation | realOrbitOrientation_trace_eq_zero | RealCoronaUniversalTransgression.lean |
| definitions of D_ev, D_odd | linearPMapOrientationEven; linearPMapOrientationOdd | RealCoronaLocalDetectabilityFracture.lean |
| parity decomposition and commutation laws | linearPMapOrientation_even_add_odd; linearPMapOrientationEven_commutes; linearPMapOrientationOdd_anticommutes | same |
| commutator equals 2 D_odd m | linearPMapOrientationCommutator_eq_two_odd | same |
| commutator norm identity | norm_linearPMapOrientationCommutator_eq_two_odd | same |
| bounded commutator iff bounded odd part | hasLinearPMapBoundOnDomain_orientationCommutator_iff_odd | same |
| bounded D iff both parts bounded | hasLinearPMapBoundOnDomain_iff_even_and_odd | same |
| full conservation equivalence | bounded_orientationCommutator_iff_unbounded_even_and_bounded_odd | same |

## Section 3: P1

| Paper identity/result | Lean declaration |
|---|---|
| actual multiplicity-copy Xi divisor and reflection | XiZeroCopy; xiZeroCopyReflectEquiv |
| reflection-invariant energy | xiCompleteDivisorEnergy_reflect |
| maximal odd divisor operator | xiCompleteDivisorOddDirac |
| self-adjointness | xiCompleteDivisorOddDirac_isSelfAdjoint |
| genuine unboundedness | xiCompleteDivisorOddDirac_genuinelyUnbounded |
| orientation domain invariance and oddness | xiCompleteDivisorOrientation_mem_oddDomain; xiCompleteDivisorOddDirac_orientation_odd |
| inverse-energy summability | summable_norm_xiCompleteDivisorInverseWeight_sq |
| bounded two-sided inverse | xiCompleteDivisorOddInverse; xiCompleteDivisorOddDirac_inverse_left; xiCompleteDivisorOddDirac_inverse_right |
| inverse Hilbert--Schmidt and compact | xiCompleteDivisorOddInverse_isHilbertSchmidt; xiCompleteDivisorOddInverse_isCompact |
| exact projector idempotence | xiCompleteDivisorRealCoronaProjector_isIdempotent |
| projector commutator norm identity | norm_xiCompleteDivisorOdd_projectorCommutator |
| projector not Lipschitz | xiCompleteDivisorOdd_not_realCoronaProjector_lipschitz |
| bundled P1 certificate | xiCompleteDivisorOdd_zetaNoGo_certificate |

Module: RealCoronaCompleteDivisorOddZetaNoGo.lean.

## Section 4: literal closed CCM recipient and P2

### Literal target and landing

| Paper identity/result | Lean declaration/module |
|---|---|
| nonunital continuous trace-class field algebra | CCMRationalContinuousTraceNormIdealField / CCMRationalNonunitalStrongCyclicTarget.lean |
| single global unitization | CCMRationalContinuousTraceNormIdealFieldUnitization / same |
| global augmentation cyclic kernel | ccmRationalNonunitalFieldAugmentationCyclicHom / same |
| diagonal trace modulo exact strong space | ccmRationalNonunitalFieldStrongQuotientTraceCyclicHom / same |
| literal double-kernel target | CCMRationalNonunitalStrongCyclicTarget; mem_ccmRationalNonunitalStrongCyclicTarget_iff / same |
| exact reduced nonunital restriction | ccmRationalAdelicReducedNonunitalStrongCyclicHom / CCMRationalAdelicNonunitalStrongCyclicHom.lean |
| periodic all-weight decay | ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay / CCMRationalPeriodicResidueSchwartzStrongLogDecay.lean |
| common-period packet and endpoint identities | ccmRationalAdelicTensor_exists_periodicTracePacket; CCMRationalAdelicTensorPeriodicTracePacket.physicalZeroMode_eq; CCMRationalAdelicTensorPeriodicTracePacket.dualZeroMode_eq |
| finite-adelic Haar quadrature | ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_nsmul_integral |
| profinite local constancy | ccmRationalAdelicTensorUnitLogTrace_isLocallyConstant |
| weighted-shift trace norm | ccmRationalMoritaWeightedShift_traceNorm_eq_lOne |
| trace formula and multiplicativity | ccmRationalAdelicMoritaRepresentation_opTrace_eq_orbitSum; ccmRationalAdelicMoritaRepresentation_mul |
| all-degree total-product reduction | ccmRationalStrongDiagonalTrace_source_eq_totalProduct; ccmRationalAdelicEpsilonZeroCyclic_eq_totalProduct; ccmRationalAdelicEpsilonOneCyclic_eq_totalProduct |
| literal all-degree landing | ccmRationalAdelicReducedNonunitalStrongCyclicDegree; ccmRationalAdelicReducedNonunitalStrongCyclicHom |

### Closed quotient, boundary law, and separator

| Paper identity/result | Lean declaration |
|---|---|
| literal closed quotient | CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule |
| closed range and projection | CCMRationalAdelicClosedNonunitalStrongRestrictionRange; ccmRationalAdelicClosedNonunitalStrongRelativeCyclicProjection |
| finite-fibre Haar averaging | ccmRationalStrongClassSpace_exists_haarAverage |
| tensor boundary equality | ccmRationalStrongClassSpaceTrivialMellinLM_tensor_eq_boundary |
| every reduced value factors through a Meyer boundary | ccmRationalAdelicReducedNonunitalStrongHaarMellin_exists_boundary |
| zeta-zero annihilation | ccmRationalAdelicReducedNonunitalStrongHaarMellin_zero_at_zeta_zero |
| Gaussian strong chain | ccmRationalNonunitalLogGaussianStrongChain |
| exact Gaussian Mellin transform and nonvanishing | deningerMeyerLogGaussianSource_mellin; ccmRationalNonunitalStrongHaarMellinLM_logGaussian_ne_zero |
| continuous functional kills closed range | ccmRationalAdelicClosedNonunitalStrongRestrictionRange_le_mellinKer |
| unconditional nonzero quotient class | ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero |

Modules: CCMRationalAdelicClosedNonunitalStrongLefschetz.lean,
CCMRationalAdelicHaarMellinBoundaryLaw.lean,
CCMRationalNonunitalStrongHaarMellinSeparator.lean, and
DeningerMeyerPoissonMellinFactorization.lean.

### Lefschetz, Real parity, and Clifford survivor

| Paper identity/result | Lean declaration |
|---|---|
| descended invertible Lefschetz action | ccmRationalAdelicClosedNonunitalStrongLefschetz; ccmRationalAdelicClosedNonunitalStrongLefschetz_leftInverse_degree |
| source/target actions, continuity, and exact equivariance | ccmRationalAdelicTwistedReducedSourceCyclicClassSpaceRightAction; ccmRationalNonunitalStrongCyclicRightActionDegree_continuous; ccmRationalAdelicReducedNonunitalStrongCyclicHom_classSpaceRightAction |
| quotient action law and identity | ccmRationalAdelicClosedNonunitalStrongLefschetz_mul_degree; ccmRationalAdelicClosedNonunitalStrongLefschetz_one_degree |
| descended even Real structure | ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal |
| Lefschetz Real-even | ccmRationalAdelicClosedNonunitalStrongLefschetzKReal |
| every Lefschetz translation nonzero | ccmRationalAdelicClosedNonunitalStrongLefschetz_degreeZero_nonzero |
| even and anti-Real forces zero | CyclicModule.KRealHom.degree_eq_zero_of_anti |
| Lefschetz not anti-Real | ccmRationalAdelicClosedNonunitalStrongLefschetz_not_antiReal |
| zL anti-Real iff conj z = -z | ccmRationalAdelicClosedNonunitalStrongLefschetz_smul_isAnti_iff_star_eq_neg |
| no anti-Real character equals Lefschetz | ccmRationalAdelicClosedNonunitalStrong_no_antiRealCharacter_eq_lefschetz |
| arbitrary bivariant realization no-go | ccmRationalAdelicClosedNonunitalStrong_no_bivariantChernRealization_eq_lefschetz |
| Clifford transgression equals iL | ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_eq_i_lefschetz |
| identity transgression squares to minus identity | ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_one_sq |

## Section 5: P3

| Paper identity/result | Lean declaration |
|---|---|
| dense endpoint-holomorphic algebra | endpointHolomorphicSubalgebra; endpointHolomorphicSubalgebra_dense |
| exact corona idempotent | endpointRealCoronaIdempotent; endpointRealCoronaIdempotent_isIdempotent |
| finite-sector coefficient classification | endpointRealCoronaIdempotent_mem_iff_finite |
| reflection crossed product and dense inclusion | HolomorphicDivisorReflection; reflectedEndpointCrossedProduct_denseRange |
| crossed-product finite-sector classification | reflectedEndpointCorona_crossedProduct_iff_finite |
| finite-zero subquadratic normal form | exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet |
| growth forces infinitely many zeros | zeroSet_infinite_of_subquadratic_superlinear_ray |
| certified analytic interface | PositiveDegreeSelfDualCompletion |
| derived complete-strip divisor and no-go | PositiveDegreeSelfDualCompletion.toCompleteStripReflectionDivisor; PositiveDegreeSelfDualCompletion.corona_not_mem_smoothCrossedProductRange |
| universal sector infinitude and accumulation | CompleteStripReflectionDivisor.upperSector_infinite; CompleteStripReflectionDivisor.lowerSector_infinite; CompleteStripReflectionDivisor.zero_mem_closure_upper; CompleteStripReflectionDivisor.zero_mem_closure_lower |
| actual Xi no-go | xiCompactifiedCorona_not_mem_smoothCrossedProductRange |
| actual primitive self-dual Dirichlet no-go | selfDualPrimitiveDirichlet_corona_not_mem_smoothCrossedProductRange |
| positive Xi-power sectors equal Xi | xiPowerCompactifiedUpperZeroSector_eq; xiPowerCompactifiedLowerZeroSector_eq |
| degree-zero Xi-power sectors empty | xiPowerCompactifiedUpperZeroSector_zero; xiPowerCompactifiedLowerZeroSector_zero |
| exact all-degree Xi-power classification | xiPowerAllDegree_corona_mem_smoothCrossedProductRange_iff |

## Section 6: P4

| Paper identity/result | Lean declaration |
|---|---|
| self-dual analytic family and reflected orders | CompletedSelfDualAnalyticFamily; CompletedSelfDualAnalyticFamily.analyticOrderAt_reflect |
| central parity/root number | CompletedSelfDualAnalyticFamily.centralParity_sign |
| finite real-window multiplicity | CompletedSelfDualAnalyticFamily.realWindowZeroSet_finite |
| pointwise defect decomposition | CompletedSelfDualAnalyticFamily.defectRank_eq_orderAt_center_add_twice_upper |
| K0 support and multiplicity excess | fixedSectorDefectRank_eq_kZeroRank_add_multiplicityExcess |
| signed defect variation | CompletedSelfDualAnalyticFamily.fixedSectorDefectVariation_eq |
| analytic-rank variation = K0 + excess | CompletedSelfDualAnalyticFamily.analyticRankVariation_eq_kZero_add_excess |
| fixed Fourier equivalence | fixedReflectionFourierRingEquiv |
| coefficient/idempotent diagonal images | fixedReflectionFourierRingEquiv_coefficient; fixedReflectionFourierRingEquiv_realCoronaIdempotent |
| crossed-product idempotence | realCoronaFixedCrossedProductIdempotent_isIdempotent |
| crossed-product K0 class/map | realCoronaFixedCrossedProductKZeroClass; fixedCoordinateToReflectionCrossedProductKZero |
| both characters see support | fixedReflectionCrossedProductKZeroPlusEvaluationRank_realCoronaClass; fixedReflectionCrossedProductKZeroMinusEvaluationRank_realCoronaClass |
| equality with rank iff rank at most one | CompletedSelfDualAnalyticFamily.centralFixedCrossedPlusKZero_eq_analyticRank_iff; CompletedSelfDualAnalyticFamily.centralFixedCrossedMinusKZero_eq_analyticRank_iff |
| concrete entire family | polynomialCompleted; polynomialSelfDualFamily |
| exact orders at 0, 1, -1 | polynomialCompleted_order_zero; polynomialCompleted_order_one; polynomialCompleted_order_neg_one |
| exact real-window divisor | polynomialSelfDualFamily_realWindowMultiplicity |
| concrete rank, paired part, defect | polynomialSelfDualFamily_analyticRank; polynomialSelfDualFamily_upperOffCentralMultiplicity; polynomialSelfDualFamily_defectRank |
| central K0 support | polynomialSelfDualFamily_centralKZeroRankInt |
| concrete signed variations | polynomialSelfDualFamily_fixedSectorDefectVariation; polynomialSelfDualFamily_analyticRankVariation; polynomialSelfDualFamily_upperOffCentralMultiplicityVariation; polynomialSelfDualFamily_centralKZeroVariation |

## Formal integrity gates

- Direct facade elaboration: lake env lean GaloisForLFunctions/RHTower/RealCoronaFourProblemsResolution.lean.
- Final targeted build: lake build GaloisForLFunctions.RHTower.RealCoronaFourProblemsResolution.
- Lint: python3 scripts/formal_tools.py lint from repository root.
- Axiom audit: print axioms for facade declarations from a temporary file.
- Umbrella: formal/GaloisForLFunctions/RHTower.lean imports facade and every new module.

All gates passed on 2026-08-04. Exact outputs and hostile-review disposition are recorded in
HOSTILE_REVIEW.md; manuscript is publication-ready.
