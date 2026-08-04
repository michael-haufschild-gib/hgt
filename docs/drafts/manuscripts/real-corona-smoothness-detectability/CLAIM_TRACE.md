# Claim trace

Paper: `Smoothness--detectability conservation for Real-corona orientations`

Scope rule: every result introduced by paper maps to an unconditional Lean declaration. Historical
or standard context is explicitly cited and is not used as an untracked proof premise. Facade:
`GaloisForLFunctions.RHTower.RealCoronaFourProblemsResolution`.

## Main theorems

| Paper claim | Lean declaration | Module |
|---|---|---|
| Theorem 1.1, smoothness--detectability conservation | `realCorona_smoothnessDetectabilityConservation` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.2, complete-divisor local-series no-go | `realCoronaP1_no_completeDivisor_localSeries_charge_two` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.3, strong target is not two-sided | `realCoronaP2_strongTarget_not_twoSided` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.3, Lefschetz parity no-go | `realCoronaP2_lefschetz_not_antiReal` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.3, exact scalar-shift classification | `realCoronaP2_scalarShift_antiReal_iff_star_eq_neg` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.3, Clifford comparison squares to `-1` | `realCoronaP2_cliffordLefschetz_sq_neg_one` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.4, complete-strip smoothness no-go | `realCoronaP3_completeStrip_not_smooth` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.4, positive-degree analytic completion no-go | `realCoronaP3_positiveDegreeCompletion_not_smooth` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.4, actual Riemann Xi instance | `realCoronaP3_riemannXi_not_smooth` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.4, actual self-dual primitive Dirichlet instances | `realCoronaP3_selfDualPrimitiveDirichlet_not_smooth` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.5, fixed-sector variation | `realCoronaP4_fixedSectorVariation` | `RealCoronaFourProblemsResolution.lean` |
| Theorem 1.5, analytic-rank/K0/excess variation | `realCoronaP4_analyticRankVariation_eq_kZero_add_excess` | `RealCoronaFourProblemsResolution.lean` |

## Section 2: universal law

| Paper identity/result | Lean declaration |
|---|---|
| Definitions of `D_ev`, `D_odd` | `linearPMapOrientationEven`, `linearPMapOrientationOdd` |
| `D = D_ev + D_odd` | `linearPMapOrientation_even_add_odd` |
| `D_ev m = m D_ev` | `linearPMapOrientationEven_commutes` |
| `D_odd m = -m D_odd` | `linearPMapOrientationOdd_anticommutes` |
| `[D,m] = 2 D_odd m` | `linearPMapOrientationCommutator_eq_two_odd` |
| `norm [D,m]x = 2 norm D_odd x` | `norm_linearPMapOrientationCommutator_eq_two_odd` |
| bounded commutator iff bounded odd part | `hasLinearPMapBoundOnDomain_orientationCommutator_iff_odd` |
| bounded `D` iff both parity parts bounded | `hasLinearPMapBoundOnDomain_iff_even_and_odd` |
| unbounded `D` iff at least one parity part unbounded | `genuinelyUnboundedLinearPMap_iff_even_or_odd` |
| unbounded commutator iff unbounded odd part | `genuinelyUnboundedLinearPMap_orientationCommutator_iff_odd` |
| bounded commutator plus unbounded `D` forces unbounded even part | `genuinelyUnbounded_even_of_bounded_orientationCommutator` |
| exact conservation equivalence | `bounded_orientationCommutator_iff_unbounded_even_and_bounded_odd` |

Module: `GaloisForLFunctions/RHTower/RealCoronaLocalDetectabilityFracture.lean`.

## Section 3: complete divisor and P1

| Paper identity/result | Lean declaration |
|---|---|
| complete Xi energy and maximal diagonal | `xiCompleteDivisorEnergy`, `xiCompleteDivisorDirac` |
| self-adjointness | `xiCompleteDivisorDirac_isSelfAdjoint` |
| orientation square and norm | `xiCompleteDivisorOrientation_sq`, `norm_xiCompleteDivisorOrientation` |
| domain invariance | `xiCompleteDivisorOrientation_mem_domain` |
| absolute Dirac commutes with orientation | `xiCompleteDivisorDirac_orientation_commutes` |
| absolute Dirac genuinely unbounded | `xiCompleteDivisorDirac_genuinelyUnbounded` |
| complete-divisor odd part is zero | `xiCompleteDivisor_orientationOdd_eq_zero` |
| signed Dirac and self-adjointness | `xiCompleteDivisorSignedDirac`, `xiCompleteDivisorSignedDirac_isSelfAdjoint` |
| signed Dirac genuinely unbounded | `xiCompleteDivisorSignedDirac_genuinelyUnbounded` |
| reflection is odd for signed Dirac | `xiCompleteDivisorSignedDirac_reflection_odd` |
| signed reflection commutator genuinely unbounded | `xiCompleteDivisorSigned_reflectionCommutator_genuinelyUnbounded` |
| no smooth signed reflection | `not_exists_signedCompleteDivisorSmoothReflection` |
| absolute reflection all-orders smooth | `xiCompleteDivisorAbsoluteReflectionSmooth` |
| signed diagonal orientation all-orders smooth and commuting | `xiCompleteDivisorSignedOrientationSmooth`, `xiCompleteDivisorSignedDirac_orientation_commutes` |
| reflection conjugates orientation to negative | `xiCompleteDivisorReflection_conjugates_orientation` |
| extremal smoothness fracture | `xiCompleteDivisor_smoothnessDetectabilityFracture` |
| positive local words vanish | `linearPMapSmoothElementOfCommutes_localJetWord_eq_zero` |
| arbitrary positive local series and value | `PositiveLocalJetSeriesFormula`, `PositiveLocalJetSeriesFormula.value` |
| arbitrary positive local series vanishes | `PositiveLocalJetSeriesFormula.value_eq_zero_of_commutes` |
| summable reflection-odd total vanishes | `tsum_eq_zero_of_equiv_odd` |
| complete Xi oriented total vanishes | `tsum_xiCompleteDivisorOrientation_mul_eq_zero` |
| finite packet cancellation | `sum_xiCompleteDivisorOrientation_mul_eq_zero` |
| complete local series and value | `CompleteDivisorLocalSeriesFormula`, `CompleteDivisorLocalSeriesFormula.value` |
| every complete local series vanishes | `CompleteDivisorLocalSeriesFormula.value_eq_zero` |
| no local series has charge two | `not_exists_completeDivisorLocalSeriesFormula_value_two` |
| two-orbit graded charge equals two | `gradedMatrixTrace_realCoronaMatrixGrading_self` |

Modules: `RealCoronaCompleteDivisorDetectability.lean`,
`RealCoronaCrossedProductSmoothnessFracture.lean`, `RealCoronaLocalCyclicNoGo.lean`, and
`RealCoronaQuaternionicCyclic.lean`.

## Section 4: exact CCM target and P2

### Source, endpoints, and strong landing

| Paper identity/result | Lean declaration/module |
|---|---|
| Lemma 4.x, periodic derivative formula and smoothness | `iteratedDeriv_ccmRationalPeriodicWeightedLogTrace`, `contDiff_ccmRationalPeriodicWeightedLogTrace` / `CCMRationalPeriodicWeightedStrongLogDecay.lean` |
| Lemma 4.x, global residue-family strong decay | `ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay` / `CCMRationalPeriodicResidueSchwartzStrongLogDecay.lean` |
| global exponential-weight supremum form | `DeningerMeyerStrongLogDecay.weighted_iteratedDeriv_isBounded` / `DeningerMeyerStrongLogTarget.lean` |
| Lemma 4.x, exact common-period packet | `CCMRationalAdelicTensorPeriodicTracePacket`, `ccmRationalAdelicTensor_exists_periodicTracePacket` / `CCMRationalAdelicTensorPeriodicTracePacket.lean` |
| packet physical and dual endpoint laws | `CCMRationalAdelicTensorPeriodicTracePacket.physicalZeroMode_eq`, `CCMRationalAdelicTensorPeriodicTracePacket.dualZeroMode_eq` |
| profinite cyclic quotient and exact Haar quadrature | `ccmRationalZModEquivProfiniteIntegerQuotient`, `ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_nsmul_integral` |
| finite Bruhat denominator/residue Haar packet | `CCMRationalFiniteBruhatCyclicHaarPacket`, `ccmRationalFiniteBruhat_exists_cyclicHaarPacket` |
| rational-to-unit orbit reindexing | `ccmRationalAdelicBruhatTensorOrbitSum_eq_unitOrbitSum` |
| whole-profile profinite local constancy | `ccmRationalAdelicTensorUnitLogTrace_isLocallyConstant` |
| exact weighted-shift trace norm | `ccmRationalMoritaWeightedShift_traceNorm_eq_lOne`, `ccmRationalMoritaWeightedShift_traceNorm_sub_eq_lOne` / `CCMRationalWeightedShiftTraceNormBound.lean` |
| weighted-shift trace and representation trace formula | `ccmRationalMoritaWeightedShift_opTrace`, `ccmRationalAdelicMoritaRepresentation_opTrace_eq_orbitSum` |
| weighted-shift composition/crossed-product law | `ccmRationalMoritaWeightedShift_comp`, `ccmRationalAdelicMoritaRepresentation_mul` |
| all-degree ordered-total-product reduction | `ccmRationalStrongDiagonalTrace_source_eq_totalProduct`, `ccmRationalAdelicEpsilonZeroCyclic_eq_totalProduct`, `ccmRationalAdelicEpsilonOneCyclic_eq_totalProduct` |
| zero-adele trace and all-degree endpoint | `ccmRationalAdelicEpsilonZero`, `ccmRationalAdelicEpsilonZeroCyclic` / `CCMRationalAdelicEpsilonZero*.lean` |
| finite-adelic Haar character `abs(q)_infinity^-1` | `ccmRationalFiniteAdeleScalingHaarCharacter`, `ccmRationalFiniteBruhatIntegral_scaling` / `CCMRationalFiniteAdeleHaarCharacter.lean` |
| genuine epsilon-one trace and cyclic endpoint | `ccmRationalAdelicEpsilonOne`, `ccmRationalAdelicEpsilonOneCyclic` / `CCMRationalAdelicEpsilonOne*.lean` |
| exact nested reduced source | `CCMRationalAdelicReducedSourceCyclicModule` / `CCMRationalAdelicEpsilonOneCyclic.lean` |
| trace-class Morita representation | `ccmRationalAdelicMoritaRepresentation`, `ccmRationalAdelicMoritaRepresentation_mul`, `ccmRationalAdelicMoritaRepresentation_isTraceClass` / `CCMRationalAdelicMoritaRepresentation.lean` |
| actual class-space cyclic restriction | `ccmRationalAdelicClassSpaceCyclicHom`, `ccmRationalAdelicReducedClassSpaceCyclicHom` / `CCMRationalAdelicClassSpaceCyclicModule.lean` |
| exact strong diagonal cyclic submodule | `ccmRationalStrongCyclicObjectSubmodule` / `CCMRationalStrongCyclicTarget.lean` |
| common-period residue packet | `ccmRationalAdelicTensorPeriodicTracePacket` family / `CCMRationalAdelicTensorPeriodicTracePacket.lean` |
| local constancy in profinite coordinate | `ccmRationalAdelicTensorUnitLogTrace_isLocallyConstant` |
| degree-zero exact strong landing | `ccmRationalAdelic_sourceClassSpaceTrace_mem_strong_of_endpoints` |
| all-degree exact strong landing | `ccmRationalAdelic_reduced_source_image_mem_strong` |

### Multiplication fracture

| Paper identity/result | Lean declaration |
|---|---|
| constants are strong iff zero | `deningerMeyerStrongLogDecay_const_iff` |
| two actual weighted-shift matrix units | `ccmRationalMoritaMatrixUnitOneNeg`, `ccmRationalMoritaMatrixUnitNegOne` |
| both traces zero | `ccmRationalMoritaMatrixUnitOneNeg_trace`, `ccmRationalMoritaMatrixUnitNegOne_trace` |
| product trace one | `ccmRationalMoritaMatrixUnit_mul_trace` |
| both constant fields strong | `ccmRationalMoritaMatrixUnits_mem_strongDegreeZero` |
| product field not strong | `ccmRationalMoritaMatrixUnitProduct_not_mem_strongDegreeZero` |
| strong target not multiplicatively closed | `ccmRationalStrongDegreeZero_not_mul_closed` |
| strong target not two-sided | `ccmRationalStrongDegreeZero_not_twoSided` |
| no representative-preserving quotient multiplication | `ccmRationalStrongDegreeZero_no_descended_quotient_multiplication` |

Module: `CCMRationalStrongTraceMultiplicationFracture.lean`.

### Real parity and Clifford comparison

| Paper identity/result | Lean declaration |
|---|---|
| even and anti-Real morphism vanishes degreewise | `CyclicModule.KRealHom.degree_eq_zero_of_anti` |
| multiply Real-even morphism by `i` gives anti-Real morphism | `CyclicModule.KRealHom.cliffordTransgression` and `cliffordTransgression_degree_apply` |
| identity transgression squares to `-1` | `CyclicModule.KRealHom.cliffordTransgression_identity_sq` |
| explicit nonzero exact strong chain | `ccmRationalStrongCyclicNonzeroWitness_ne_zero` |
| every Lefschetz translation nonzero | `ccmRationalStrongCyclicLefschetz_degreeZero_nonzero` |
| no Lefschetz translation anti-Real | `ccmRationalStrongCyclicLefschetz_not_antiReal` |
| scalar shift `z L_c` is anti-Real iff `conj z = -z` | `CyclicModule.KRealHom.smul_isAnti_iff_star_eq_neg`, `ccmRationalStrongCyclicLefschetz_smul_isAnti_iff_star_eq_neg` |
| full-adeles Clifford replacement `i L_c` | `ccmRationalStrongCyclicKappaTransgression` and `_apply` |
| identity replacement squares to `-1` | `ccmRationalStrongCyclicKappaTransgression_one_sq` |

Modules: `KRealCyclicCliffordTransgression.lean` and
`CCMRationalKappaLefschetzParityNoGo.lean`.

## Section 5: endpoint smoothness and P3

| Paper identity/result | Lean declaration |
|---|---|
| endpoint-holomorphic dense subalgebra | `endpointHolomorphicSubalgebra`, `endpointHolomorphicSubalgebra_dense` |
| full divisor characteristic idempotent | `endpointRealCoronaIdempotent`, `endpointRealCoronaIdempotent_isIdempotent` |
| coefficient membership iff holomorphic separator | `endpointRealCoronaIdempotent_mem_iff` |
| upper accumulation no-go | `no_endpoint_holomorphic_rep_of_upper_accumulates` |
| lower accumulation no-go | `no_endpoint_holomorphic_rep_of_lower_accumulates` |
| finite sectors have entire Lagrange separator | `exists_entire_corona_rep_of_finite` |
| exact finite-sector classification | `endpoint_holomorphic_corona_iff_finite`, `endpointRealCoronaIdempotent_mem_iff_finite` |
| honest holomorphic reflection crossed product | `HolomorphicDivisorReflection` and `functionAction` |
| reflection sends corona to complement | `odd_smul_endpointRealCoronaIdempotent_eq_complement` |
| crossed-product inclusion has dense range | `reflectedEndpointCrossedProduct_denseRange` |
| crossed-product finite-sector classification | `reflectedEndpointCorona_crossedProduct_iff_finite` |
| finite-zero subquadratic normal form | `exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet` |
| superlinear ray forces infinite zero set | `zeroSet_infinite_of_subquadratic_superlinear_ray` |
| positive-degree analytic completion | `PositiveDegreeSelfDualCompletion` |
| positive-degree zero infinitude is derived | `PositiveDegreeSelfDualCompletion.zeroSet_infinite` |
| positive-degree local zero finiteness is derived | `PositiveDegreeSelfDualCompletion.zeros_closedBall_finite` |
| conversion to complete-strip divisor | `PositiveDegreeSelfDualCompletion.toCompleteStripReflectionDivisor` |
| positive-degree nonsmoothness | `PositiveDegreeSelfDualCompletion.corona_not_mem_smoothCrossedProductRange` |
| universal reciprocal sectors and endpoint accumulation | `CompleteStripReflectionDivisor.exists_zero_im_abs_gt`, `zero_mem_closure_upper`, `zero_mem_closure_lower`, `upperSector_infinite`, `lowerSector_infinite` |
| universal complete-strip nonsmoothness | `CompleteStripReflectionDivisor.corona_not_mem_smoothCrossedProductRange` |
| actual Xi reciprocal sectors | `xiCompactifiedUpperZeroSector`, `xiCompactifiedLowerZeroSector` |
| actual Xi accumulation, infinitude, crossed-product no-go | `zero_mem_closure_xiCompactifiedUpperZeroSector`, `zero_mem_closure_xiCompactifiedLowerZeroSector`, `xiCompactifiedUpperZeroSector_infinite`, `xiCompactifiedLowerZeroSector_infinite`, `xiCompactifiedCorona_not_mem_smoothCrossedProductRange` |
| completed primitive Dirichlet zero infinitude | `completedLFunction_zeroSet_infinite` |
| primitive Dirichlet strip confinement | `completedLFunction_zero_mem_openUnitStrip` |
| primitive Dirichlet local zero finiteness and unbounded ordinates | `completedLFunction_zeros_closedBall_finite`, `exists_completedLFunction_zero_im_abs_gt` |
| actual self-dual primitive Dirichlet divisor | `selfDualPrimitiveDirichletCompleteStripDivisor` |
| actual self-dual primitive Dirichlet nonsmoothness | `selfDualPrimitiveDirichlet_corona_not_mem_smoothCrossedProductRange` |

Modules: `RealCoronaEndpointHolomorphicSmoothness.lean`,
`RealCoronaHolomorphicReflectionCrossedProduct.lean`, `FiniteZeroSubquadraticRigidity.lean`,
`PositiveDegreeAutomorphicRealCoronaSmoothness.lean`,
`CompleteStripRealCoronaCompactification.lean`, `XiAutomorphicRealCoronaSmoothness.lean`,
`DirichletLZerosInfinite.lean`, and `SelfDualDirichletRealCoronaSmoothness.lean`.

## Section 6: fixed sector and P4

| Paper identity/result | Lean declaration |
|---|---|
| analytic self-dual family | `CompletedSelfDualAnalyticFamily` |
| reflection preserves analytic order | `CompletedSelfDualAnalyticFamily.analyticOrderAt_reflect` |
| root number squares to one | `CompletedSelfDualAnalyticFamily.rootNumber_mul_self` |
| root number is `+1` or `-1` | `CompletedSelfDualAnalyticFamily.rootNumber_eq_one_or_neg_one` |
| central order parity is root number | `CompletedSelfDualAnalyticFamily.centralParity_sign` |
| real window zero set is finite | `CompletedSelfDualAnalyticFamily.realWindowZeroSet_finite` |
| reflected multiplicities agree | `CompletedSelfDualAnalyticFamily.realWindowMultiplicity_reflect` |
| analytic rank is central analytic order | `CompletedSelfDualAnalyticFamily.analyticRank_eq_orderAt_center` |
| pointwise defect equals rank plus twice upper multiplicity | `CompletedSelfDualAnalyticFamily.defectRank_eq_orderAt_center_add_twice_upper` |
| coordinate K0 rank is support cardinality | `fixedSectorKZeroRank_eq_support_card` |
| cyclic defect is K0 rank plus multiplicity excess | `fixedSectorDefectRank_eq_kZeroRank_add_multiplicityExcess` |
| central K0 evaluation detects analytic rank only in multiplicity-free case | `CompletedSelfDualAnalyticFamily.centralKZeroEvaluation_eq_analyticRank_iff` |
| family fixed-sector variation formula | `CompletedSelfDualAnalyticFamily.fixedSectorDefectVariation_eq` |
| central K0 variation is support-indicator variation | `CompletedSelfDualAnalyticFamily.centralKZeroVariation_eq` |
| analytic-rank variation equals K0 variation plus excess variation | `CompletedSelfDualAnalyticFamily.analyticRankVariation_eq_kZero_add_excess` |
| actual self-dual primitive Dirichlet family | `selfDualPrimitiveDirichletAnalyticFamily` |
| actual Dirichlet defect/rank formula | `selfDualPrimitiveDirichlet_defectRank_eq_analyticRank_add_twice_upper` |
| actual Dirichlet rank parity/root number | `selfDualPrimitiveDirichlet_analyticRank_parity_rootNumber` |

Modules: `SelfDualAnalyticRealZeros.lean`, `RealCoronaUniversalTransgression.lean`,
`RealCoronaKZeroMultiplicityFracture.lean`, `SelfDualFixedSectorVariation.lean`, and
`SelfDualDirichletRealZeros.lean`.

## Section 7: synthesis identities

| Paper identity/result | Lean declaration |
|---|---|
| orientation square `m0^2 = 1 - eFixed` | `RealOrbitIdempotentDecomposition.orientation_sq` |
| Real parity `sigma(m0) = -m0` | `RealOrbitIdempotentDecomposition.sigma_orientation` |
| fixed idempotent `= 1 - m0^2` | `RealOrbitIdempotentDecomposition.fixed_eq_one_sub_orientation_sq` |
| crossed-product orientation is commutator | `realOrbitOrientation_eq_commutator` |
| ordinary cyclic traces kill orientation | `realOrbitOrientation_trace_eq_zero` |
| support/multiplicity collateral decomposition | `fixedSectorDefectRank_eq_kZeroRank_add_multiplicityExcess` |

## Formal integrity gates

- Facade direct elaboration: `lake env lean GaloisForLFunctions/RHTower/RealCoronaFourProblemsResolution.lean`.
- Final targeted build: `lake build GaloisForLFunctions.RHTower.RealCoronaFourProblemsResolution`.
- Lint: `python3 scripts/formal_tools.py lint` from repository root.
- Axiom audit: `#print axioms` for facade declarations from a temporary file.
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean` imports facade and all new P3 modules.

Final command outputs belong in `HOSTILE_REVIEW.md`; until those gates run, manuscript remains
in-progress.
