# Claim trace for `main-universal.tex`

Internal truth audit only.  Verification technology is not mentioned in the
manuscript and contributes nothing to novelty or significance.

Audit date: 2026-08-01.

## Policy

- Every mathematical claim in `main-universal.tex` must be an unconditional
  consequence of a declaration below or an explicit proof in the manuscript.
- RH, zero exclusion, positive source orientation, and finite-Rees reflected
  sewing are not claimed.
- “Subsumes” means exact specialization of the admission/separation defect
  ledger through a named source map.  It does not mean that the elementary
  factorization theorem supplies each analytic estimate.

## Admission--separation law

| Manuscript claim | Declaration | Module |
|---|---|---|
| Global recovery iff admission and kernel refinement | `partialCompletion_globallyRecovers_iff_admission_and_kernelRefines` | `HTGeometry/PartialCompletionAdmissionSeparationLaw.lean` |
| Postprocessing only enlarges the kernel pair | `partialCompletion_kernelPair_mono_postprocess`; `mapKernelPair_mono_of_factorsThrough` | `PartialCompletionAdmissionSeparationLaw.lean`; `CompletionKernelPairTransversalityLaw.lean` |
| Invariant completion kills a recovered odd target | `oddTarget_eq_zero_on_admitted_of_invariantPartialCompletion`; `oddTarget_eq_zero_of_factorsThrough_invariantCompletion` | same two modules |
| A sufficient transverse channel separates a nonzero reflected charge | `partialCompletion_separates_reflection_of_oddCharge_ne_zero`; `transverseChannel_separates_reflection_of_oddCharge_ne_zero` | same two modules |
| Dense completion fibres force continuous downstream reporters to be constant | `downstreamReporter_constant_of_dense_completionFibers` | `HTGeometry/CompletionKernelPairTransversalityLaw.lean` |
| Hyperbolic channel annihilates anti-invariants | `reflectionOrientation_mul_hyperbolic_eq_zero`; `hyperbolic_smul_antiInvariant_eq_zero` | `HTGeometry/ReflectionOrientationSingularSupportLaw.lean` |
| Nontrivial orientation iff hyperbolic element is nonregular | `reflectionOrientation_ne_one_iff_hyperbolic_not_regular` | same |

The elementary converse factorization and the decomposition
`v=(v+εv)/2+(v-εv)/2` are proved directly in the manuscript.

## Positive exponent-shell source and common divisor

| Manuscript claim | Declaration | Module |
|---|---|---|
| Exact largest-exponent shell and disjoint positive support | `shellIndicator_eq_one_iff`; `shellIndicator_eq_zero_of_ne` | `RHTower/HighExponentShellZeroFree.lean` |
| Shell factorization `S_m=ζH_m` | `LSeries_shellIndicator` | same |
| `H_m` analytic and zero-free on `Re s>1/2`, `m≥12` | `analyticAt_shellMultiplier`; `shellMultiplier_ne_zero` | same |
| Exact divisor-order replication | `finiteHighShell_analyticOrderReplication` | `RHTower/HighExponentShellFusionConservation.lean` |
| Relative differential independence over the zeta differential field | `finiteHighShell_relativeDifferentialIndependent`; `relativeShellMultiplierUpperEndCarrier_differentialIndependent_two` | `HighExponentShellFusionConservation.lean`; `HighExponentShellHypertranscendence.lean` |
| Infinite relative differential fibre | finite-packet theorem for every `n`, as stated above | same |

## Finite and infinite fusion

| Manuscript claim | Declaration | Module |
|---|---|---|
| Mean/centered decomposition | `finiteLabel_inner_fusion_decomposition` | `HTGeometry/CommonCharacterFusionConservation.lean` |
| Fusion kernel has codimension one | `finiteLabelFusionLinearMap_finrank_ker` | same |
| Reciprocal quadratic conservation identity | `reciprocalLabelQuadratic_fusion_conservation` | same |
| Positive diagonal and negative antidiagonal directions | `reciprocalLabelQuadratic_diag_pos`; `reciprocalLabelQuadratic_antidiag_neg` | same |
| Opposite-character reflected action preserves the form and intertwines fusion | `reciprocalLabelForm_reflectedLabelAction_invariant`; `finiteLabelFusion_reflectedLabelAction_fst`; `finiteLabelFusion_reflectedLabelAction_snd` | same |
| Shell codiagonal is not sequentially closable and Bessel unit response is impossible | `highShell_no_stableHilbert_unitFusion`; `highShell_infiniteFusionSingularity_and_unitaryLocus` | `RHTower/HighExponentShellFusionConservation.lean` |
| Route-J centered block energy is smaller than squared bad mass | `ccmFirstClockJuliaSixthPowerBlockCenteredFusionEnergy_lt_badMass_sq`; `ccmFirstClock_sourceFusion_regularHilbert_noGo` | `RHTower/CCM/CCMFirstClockSourceFusionSuperselectionNoGo.lean` |

## One centered modular charge

| Manuscript claim | Declaration | Module |
|---|---|---|
| Centered complex character is additive and has exact real-ray norm | `centeredComplexModularCharacter_add`; `centeredComplexModularCharacter_real_cpow` | `RHTower/RiemannComplexModularCharacterLaw.lean` |
| Unitary locus is exactly `Re ρ=1/2` | `norm_centeredComplexModularCharacter_ofReal`; direct proof in manuscript | same |
| Reflected real-ray norms are reciprocal | `norm_centeredComplexModularCharacter_reflection_mul`; `criticalLineReflectionPoint_weight` | same |
| Principal Hurwitz phase recovers the same charge | `centeredComplexModularCharacter_principalPhase` | same |
| Shell entropy equals centered real displacement | `shellTransferEntropy_eq` | `RHTower/XiHypertranscendentalModularResidueTransgression.lean` |
| Centered Xi residue reports shell entropy times multiplicity | `re_centeredXiAffineResidue_eq_shellTransferEntropy` | same |
| Compact-BV residue ratio reports the same charge | `xiBVResiduePhaseCoordinate_eq_sourceModularCharge` | `RHTower/XiSourceModularTypeSuperselectionLaw.lean` |

## Activation, reflected depth, and Rees superselection

| Manuscript claim | Declaration | Module |
|---|---|---|
| Diagonal activation equals `ζ(s)/ζ(2s)` | `woldActivationHolonomy_diagonal_eq_squarefreePartition` | `RHTower/EulerActivationSquarefreeDisintegration.lean` |
| Local valuation law splits occupancy and conditional geometric depth | `diagonalActivationPositiveValuationMass_factorization`; `diagonalActivationValuationMass_total` | same |
| Occupancy Fisher variance and Möbius/Gamma atoms | `diagonalActivationOccupancyFisher_eq_variance`; `diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference`; `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation` | same |
| Reflected Hellinger sector is critical, half-normal, or all-orders flat according to charge | `primeValuationHellinger_reesType_trichotomy`; `reflected_primeValuationSquaredHellinger_type_fracture` | `RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| Finite-grade matrices/operators preserve the flat radical | `reesAllOrdersFlat_finiteReesJetTransform`; `reesAllOrdersFlat_apply_reesOperatorGradeAtMost` | `RHTower/PrimeValuationHellingerReesJetStability.lean` |
| Exact reflected sewing cost exceeds every finite inverse Rees power | `xiRightModularAffinitySewingCost_beyondEveryReesOrder`; `xiRightModularAffinitySewingOperatorNorm_beyondEveryReesOrder` | `RHTower/XiSourceModularTypeSuperselectionLaw.lean` |

The finite Euler-product proof of the explicit affinity estimates is included
in the manuscript.

## Exact positive and negative specializations in Table 1

| Row | Declarations | Module |
|---|---|---|
| Wold--Poisson faithful lift | `xiWoldPoissonBivariateConormalResponse_residue_transport`; `xiWoldPoissonBivariateConormalResidueMode_eq_zero_iff` | `RHTower/XiWoldPoissonBivariateConormal.lean` |
| Holomorphic strip separation | `hull_eq_of_line_eq`; `bohrEval_injective_of_isometry` | `HTGeometry/StripHullSeparation.lean` |
| Gamma-field finite-phase boundary | `finite_phase_law_of_gammaField_relation`; `finite_phase_law_of_gammaField_coefficients_eventual` | `HTGeometry/GammaFieldCoefficientLaw.lean` |
| Hedenmalm dense radical and nonclosability | `dense_xiThetaL2RadicalImage_of_scalarThetaNull`; `universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_leftTemperedDistribution_zero`; `hilbertGram_l2PartialOperator_not_closable` | `RHTower/Hedenmalm/HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean`; `HedenmalmSourceHilbertGramClosedGraphNoGo.lean` |
| Deninger Tor and middle fibre | `deningerTor_injective`; `deningerTor_map_eq`; `deningerMiddleFiber_degree_zero`; `deningerMiddleFiber_degree_one_injective`; `deningerMiddleFiber_degree_one_surjective`; `deningerMiddleFiber_degree_two` | `RHTower/Deninger/DeningerKummerStalkTor.lean`; `DeningerMiddleFiber.lean` |
| Deninger finite-prime endpoint | `deningerSOrd_product`; `deningerSEndpoint_H0`; `deningerSEndpoint_H1`; `deningerSEndpoint_H2` | `RHTower/Deninger/DeningerSUnitEndpointPage.lean` |
| Arithmetic cyclotomic comparison and nontrivial quotient | `deningerPrimeArithmeticCyclotomicCharacter_range`; `deningerPacketFrobeniusClosure_ne_top` | `DeningerPrimeArithmeticCyclotomicComparison.lean`; `DeningerPacketFrobeniusQuotientNontrivial.lean` |
| Real twisted orientation and Rees jets | `deningerRealTwist_forced`; `deningerGermJ_flow_comm`; `deningerRealJet_reesFlow`; `deningerJetTower_tsum`; `deningerGermJetTower_character` | `DeningerRealApexEndpoint.lean`; `DeningerReesJetTower.lean`; `DeningerStationaryKahlerGerm.lean` |
| Deninger flow purity and Green radical | `deningerFlowPurity_re_eq`; `deningerLeafHodgeJ_pos`; `deningerPrimePacketContinuousRestrictionSummedGreenForm_self_eq_zero_iff` | `DeningerKahlerRiemannFlowPurity.lean`; `DeningerPrimePacketContinuousRestrictionGreen.lean` |
| Sonin linear completion boundary | `not_sublinear_of_forall_bddBelow` | `RHTower/SoninCompletionMustGrowLinearly.lean` |
| Suzuki phase erasure | `tendsto_suzukiCompactCoreDeficiencyProjection_zero`; `tendsto_suzukiApertureCayley_allBoundarySchedules`; `tendsto_suzukiApertureResolvent_allBoundarySchedules` | `RHTower/Suzuki/SuzukiCompactCorePhaseUniversality.lean` |
| Free Suzuki interface | `exists_suzukiEdgeData_of_operator`; `nonempty_suzukiEdgeData` | `RHTower/Suzuki/SuzukiEdgeDataInterface.lean` |
| Trace-class valuation correction | `routeKPhysicalEndpointCorrectionOperator_memSchattenClass_one` | `RHTower/XiPrimeMarkedPhysicalEndpointCorrectionTraceClass.lean` |
| Primitive boundary is not absolutely nuclear | `not_summable_norm_routeKPhysicalEndpointBoundaryRankOne` | `RHTower/XiPrimeMarkedPhysicalEndpointBoundaryNuclearObstruction.lean` |
| Polynomially moderate scalar boundary | `exists_norm_seamFluxCochain_boundary_global_le` | `RHTower/XiPrimeMarkedPhysicalEndpointBoundaryGrowth.lean` |
| Source-defined trace-class relocation preserves triangles | `schattenDoubleCommutator_memSchattenClass_one`; `schattenDoubleCommutator_triangleHolonomy_ne_zero` | `RHTower/SchattenDoubleCommutatorRelocation.lean` |
| Sharp-window terminal collision | `squarePrimeWindowPositiveExcessSquare_abscissa_eq_intrinsicXiWidth`; `riemannHypothesis_of_squarePrimeWindowPositiveExcessSquareEnergySubpower` | `RHTower/CCM/CCMSharpPrimeWindowSquareEnergyWidthCollision.lean`; `CCMSharpPrimeWindowSquarePositiveExcessDuality.lean` |

## Biaxial theorem

Theorem `thm:frontier` uses exactly four implications:

1. unit shell response plus orthogonal/Bessel realization invokes
   `highShell_no_stableHilbert_unitFusion`;
2. nonzero right modular charge plus finite-Rees sewing invokes
   `xiRightModularAffinitySewingOperatorNorm_beyondEveryReesOrder`;
3. invariant scalarization of an odd charge invokes
   `oddTarget_eq_zero_on_admitted_of_invariantPartialCompletion`;
4. independence of breadth and depth follows because the first obstruction
   holds at zero charge, while the second requires nonzero charge.

No converse existence theorem is asserted.

## Final forbidden-claim gate

Reject the manuscript if it says any of:

- every modular character is unitary;
- the biaxial theorem excludes an off-line zero;
- every Hilbert--Pólya or CCM architecture satisfies its four hypotheses;
- singular sewing supplies the missing positive orientation;
- the elementary admission/separation factorization is the novelty;
- the whole corpus is literally deduced from one set-theoretic proof.
