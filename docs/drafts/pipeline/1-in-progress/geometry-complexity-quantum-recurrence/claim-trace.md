# Internal claim ledger

Not part of submitted paper. Audit date: 28 August 2026.

## Admission rule

Every result-bearing sentence, displayed identity, theorem, corollary and
proof dependency in `main.tex`, `body.tex`, `new-appendices.tex` and the
included prior-results appendix must be an exact specialization or a direct
logical composition of checked declarations below. No mathematical result is
admitted on a paper-only proof. Definitions, literature summaries and scope
exclusions are not theorem claims. Public manuscript contains no project,
proof-assistant or internal-corpus references.

## New synthesis and singularity

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| Universal stationary survival-recurrence law: arbitrary-spectrum centered-window weak convergence; exact scaling by squared total pure-point mass; one-interval support; recovery of pure-point mass from upper edge | `RHTower.universalStationarySurvivalRecurrenceLaw` | `UniversalStationaryRecurrenceLaw.lean` |
| Universal completed-return occupation law: for every finite energy list, the small-target Haar exponent exists, equals projective orbit dimension and rational temporal rank, and plus exact balanced-relation rank equals `D-1`; includes all-degenerate boundary and local bi-Lipschitz metric stability | `HTGeometry.projectiveRecurrenceOccupation_constraint_conservation`; `HTGeometry.tendsto_log_completedPhaseReturnFraction_div_log`; `HTGeometry.tendsto_log_haar_biLipschitzReturn_div_log` | `UniversalRecurrenceOccupationConservationLaw.lean` |
| Projective characters, detuning, relation lattice, temporal rank, hull dimension, character constancy, replica height, `tau+rho=D-1` | `HTGeometry.finiteProjectiveRecurrence_universalLaw` | `UniversalProjectiveRecurrenceCapstoneLaw.lean` |
| Finite-device operational bridge: normalized Kraus evolution and Schrödinger--Heisenberg Born duality; explicit reset-mixture channel; exact affine Born law; one-step device-to-unitary error at most `1-r`; `N`-step error at most `N(1-r)` | `RHTower.FiniteKrausChannel.quantumProbability_after`; `RHTower.quantumProbability_resetMixed_eq_convex`; `RHTower.resetMixedKrausChannel_oneStep_distance_unitary_le`; `RHTower.resetMixedKrausChannel_iterate_distance_unitary_le` | `FiniteQuantumOperationalMemoryLaw.lean`; `FiniteKrausRecurrenceFutureFanLaw.lean` |
| Arbitrarily weak diagonal operator-Schmidt-rank-one interaction; uncoupled rank at most `m+n`; coupled rank `mn+m+n`; gain at least `mn`; norm budget; dimension-free Heisenberg bound; every positive full-support replica collision floor | `HTGeometry.exists_smallSeparableInteraction_temporalDimensionMultiplication` | `SeparableInteractionTemporalDimensionLaw.lean` |
| General diagonal bipartite-interaction formulation used by proof narrative | `HTGeometry.exists_arbitrarilyWeak_bipartiteInteraction_fullRecurrenceCompletion` | `WeakInteractionRecurrenceSingularityLaw.lean` |

## Universal information hierarchy and strict quotient

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| One capstone joining carrier, finite/countable action limits, constraint-capacity conversion, scalar quotients, resolved completeness and strictness | `RHTower.universalQuantumRecurrenceInformationHierarchyLaw` | `UniversalQuantumRecurrenceInformationHierarchyLaw.lean` |
| Finite phase-law convergence iff every integer-character observer-action coefficient converges | `HTGeometry.existsUnique_finitePhaseLimit_iff_completeObserverActionLimits` | `UniversalObserverActionLaw.lean` |
| Countable phase-law convergence iff every finite-support character coefficient converges | `HTGeometry.existsUnique_countablePhaseLimit_iff_completeObserverActionLimits` | `UniversalObserverActionLaw.lean` |
| Zero-action characters are exact rational constraints; temporal dimension plus zero-constraint rank equals full projective capacity | `HTGeometry.phaseLawConstraintRationalSpace_eq_observerActionZero`; `HTGeometry.observerAction_temporalDimension_add_zeroConstraintRank` | `UniversalObserverActionLaw.lean` |
| Spectral difference measure is exact maximal system quotient for scalar survival under every probability clock | `RHTower.spectralDifferenceMeasure_eq_iff_allClockReturnLaws` | `ObserverRecurrenceDistributionLaw.lean` |
| Reflection-symmetrized clock law is exact maximal clock quotient for scalar survival under every probability spectrum | `RHTower.clockOrientationQuotient_eq_iff_allReturnLaws` | `ObserverRecurrenceDistributionLaw.lean` |
| Complete resolved replica detector hierarchy is equivalent to full projective relation lattice | `HTGeometry.relationLattice_eq_iff_all_resolvedReplicaDetectors_eq` | `ResolvedRecurrenceRelationCompletenessLaw.lean` |
| Product/reflection fidelity identity for arbitrary finite factor weights and energies | `RHTower.finiteSpectralSurvivalFidelity_productReflection` | `QuantumRecurrenceScalarResolvedSeparationLaw.lean` |
| Explicit uniform nine-level pair: equal scalar fidelity at every time, equal law under every probability clock, unequal relation lattices and finite resolved separation | `RHTower.quantumRecurrence_scalarResolved_strictSeparation`; component declarations `recurrenceHomometric_normSq_charFun_eq`, `recurrenceHomometric_allClockReturnLaws_eq`, `recurrenceHomometric_relationLattices_ne`, `recurrenceHomometric_exists_resolvedDetector_separation` | `QuantumRecurrenceScalarResolvedSeparationLaw.lean` |

## Law I: carrier and arbitrary spectra

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| Finite contraction peripheral decomposition and vanishing transient | `RHTower.finiteContraction_returnAmplitude_eq_persistent_sum_add_transient` | `DissipativeQuantumReturnInformationTransition.lean` |
| Exact late-time ceiling and threshold dichotomy | `RHTower.finiteContraction_returnAmplitude_exactAsymptoticCeiling`; `RHTower.finiteContraction_returnThreshold_dichotomy` | same |
| Post-burn-in target and reverse-water deadline | `RHTower.finiteContraction_exists_return_at_target_before_waterDeadline` | same |
| Arbitrary-spectrum collision hierarchy and continuous fidelity-statistic means | `RHTower.spectralReturnMomentMeanReal_tendsto_collisionHierarchy`; `RHTower.exists_tendsto_spectralReturnStatisticMeanReal` | `ObserverRecurrenceDistributionLaw.lean` |
| Finite-spectrum fixed-moment certificate: exact collision-mass plus sinc-remainder decomposition and error at most `min 1 (T * delta)⁻¹` under a positive lower bound on nonzero order-`m` replica detunings; unit constant independent of dimension and moment order | `HTGeometry.finiteSpectralSurvivalFidelityMean_eq_collisionMass_add_remainder`; `HTGeometry.norm_fidelityReplicaFiniteWindowRemainder_le`; `HTGeometry.norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le` | `FiniteWindowReplicaCollisionResolution.lean` |
| Arbitrary-spectrum stationary law has support exactly one interval ending at squared total point-spectrum mass; endpoint belongs to support, dominates it, and total point mass is its square root | `RHTower.universalStationaryRecurrenceNoGapBoundStateMassLaw`; components `RHTower.exists_stationarySpectralReturnProbabilityMeasure_support_Icc`, `RHTower.pointSpectrumFidelityScale_one_is_stationarySupportMaximum`, `RHTower.pointSpectrumMassReal_eq_sqrt_stationarySupportEdge` | `StationaryRecurrenceSupportIntervalLaw.lean` |
| Countable pure-point deficit identity, reflected relation-hull law and exact interval support used in proof | `RHTower.one_sub_normSq_countablePurePointSurvivalAmplitude_eq_screwSeries`; `RHTower.countablePurePointStationaryFidelityLaw_support`; `RHTower.stationarySpectralReturnProbabilityMeasure_support_of_countablyCarried` | `StationaryRecurrenceSupportIntervalLaw.lean` |
| Exact stationary point-spectrum scaling and atomless zero-law branch | `RHTower.stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum`; `RHTower.stationarySpectralReturnProbabilityMeasure_eq_zero_of_noAtoms` | `StationaryRecurrencePointSpectrumScalingLaw.lean`; `StationaryRecurrenceCompletionLaw.lean` |
| Countable pure-point recurrence | `RHTower.exists_summablePhaseEnergy_recurrence` | `SummablePurePointPhaseRecurrence.lean` |
| Positive exact return iff visible group is cyclic | `RHTower.exists_positive_unitFidelity_iff_cyclic` | `ObserverTemporalUniversalityLaw.lean` |
| Atomless continuum dimension and vanishing fixed return-window density | `RHTower.atomlessProjectiveObserverTemporalPhaseLaw`; packaged in `RHTower.universalQuantumRecurrenceAnatomyLaw` | `ObserverTemporalUniversalityLaw.lean`; `UniversalQuantumRecurrenceAnatomyLaw.lean` |

## Law II: local networks, thermodynamics and replicas

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| One dense, residual, full-measure coefficient set works for every induced subsystem | `HTGeometry.allSubsystemGenericSet_dense_residual_fullMeasure` | `SubsystemComponentWitness.lean` |
| Exact subsystem component formula and connected rank `D-1` | `HTGeometry.anchoredTemporalRank_subsystemHamiltonian_of_generic`; `HTGeometry.finiteGraphTemporalRank_add_one_of_connected` | `SubsystemComponentWitness.lean`; `FiniteGraphTemporalCurvatureLaw.lean` |
| One conull set in every open simple-spectrum qudit-path chart simultaneously has maximal projectivity, stroboscopic exponent `D-1`, first-gap-clock exponent `D-2`, every positive-weight replica floor and zero-only exact anchored return | `HTGeometry.exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw` | `QuditPathRecurrenceCollisionCapstone.lean` |
| Same local Hamiltonian additionally has exact physical survival-fidelity first-return exponent `(D-2)/2` for every normalized cyclic state and every positive cutoff; locality and chart existence discharged; closed shifted capstone has no proposition-valued side hypotheses | `HTGeometry.ae_tendsto_log_orbitFidelityReturnTime_sortedSpectrum`; `HTGeometry.quditPathPhysicalRecurrenceCollisionLaw_of_two_le`; `HTGeometry.universalQuditPathPhysicalRecurrenceCollisionLaw` | `QuditPathPhysicalRecurrenceCollisionLaw.lean` |
| One common conull local-Hamiltonian set classifies every normalized state simultaneously by exact nonzero spectral-support size `s`: physical survival-fidelity first-return exponent is `max(s-2,0)/2`, with exact periodic exponent-zero strata at `s=1,2`; support compression, all-support finite intersection, locality and chart existence are discharged; closed shifted capstone has no proposition-valued side hypotheses | `HTGeometry.tendsto_log_fidelityReturnTime_supportCard`; `HTGeometry.ae_all_supportGapRatio_not_vwa`; `HTGeometry.ae_tendsto_log_orbitFidelityReturnTime_supportCard_sortedSpectrum`; `HTGeometry.quditPathAllStateSupportRecurrenceLaw_of_two_le`; `HTGeometry.universalQuditPathAllStateSupportRecurrenceLaw` | `AllStateSpectralSupportRecurrenceLaw.lean` |
| Horizon-free vanishing-tail preparation instability on same local-Hamiltonian event: anchor-doped pure state is normalized and has anchor fidelity at least `1-η`; its survival deficit is at most `4η` for every real time, every resolution `δ>4η` gives return functional exactly equal to cutoff, yet every fixed `η>0` has maximal exact-resolution exponent `(D-2)/2`; locality, chart existence and unconditional shifted capstone are discharged | `HTGeometry.spectralReturnDeficit_anchorDopedWeights_le`; `HTGeometry.fidelityReturnTime_anchorDopedWeights_eq_cutoff`; `HTGeometry.finitePureStateFidelity_anchorDopedState`; `HTGeometry.tendsto_log_orbitFidelityReturnTime_anchorDopedState`; `HTGeometry.ae_vanishingTailPreparationInstability_sortedSpectrum`; `HTGeometry.quditPathVanishingTailPreparationInstabilityLaw_of_two_le`; `HTGeometry.universalQuditPathVanishingTailPreparationInstabilityLaw` | `VanishingTailRecurrenceExponentInstabilityLaw.lean` |
| Dirichlet first-hit upper bound and exact non-VWA logarithmic exponent | `HTGeometry.firstHit_le`; `HTGeometry.tendsto_log_firstHit_div_log` | `SimultaneousDirichlet.lean`; `FirstHitExponentLaw.lean` |
| Path affine spectral escape, leaf-extension rigidity and connected lifted transition graph used in sharp-clock proof | `HTGeometry.exists_quditPathChain_spectrumEscapes`; `HTGeometry.hermitianLocalExtensionSlice_spectrumEscapesAffineRelations`; `HTGeometry.hermitianLocalExtension_constantAction_coefficients_constant`; `HTGeometry.crossLayer_eq_of_selectedLayerAnalyticBranchConstantAction`; `HTGeometry.crossLayerLiftGraph_preconnected_of_two_le_card` | `QuditPathChainEscape.lean`; `AffineSpectrumRelationEscape.lean`; `HermitianLocalExtensionRelationEscape.lean`; `LocalSelectedLayerSpectralResponse.lean`; `CrossLayerLiftParityRigidity.lean` |
| Nondegenerate chart gap maps have almost-everywhere discrete and first-gap-clock exponent laws | `HTGeometry.ae_tendsto_log_firstHit_sortedGap`; `HTGeometry.ae_tendsto_log_firstHit_sortedGapRatio` | `SpectralRecurrenceExponentLaw.lean` |
| Exact commuting l-bit rank equals rational coefficient-span dimension; fixed-range geometric ceiling, sharp allowed-support criterion and uniform-state all-order visibility | `HTGeometry.lbitTemporalRank_eq`; `HTGeometry.lbitTemporalRank_add_relationRank`; `HTGeometry.lbitTemporalRank_le_geometric_linear`; `HTGeometry.lbitTemporalRank_eq_geometricSupports_card`; `HTGeometry.lbitUniformStateVisibleTemporalRank_eq`; `HTGeometry.lbitUniformState_all_survivalFidelityMoments_extremal_iff` | `LBitTemporalDimensionLaw.lean`; `LBitRecurrenceConstraintLaw.lean`; `LBitGeometricLocalityLaw.lean`; `LBitUniformStateRecurrenceLaw.lean` |
| Component-merger product law and exact rank gain | `HTGeometry.temporalRank_merge_components`; `HTGeometry.temporalRank_merge_gain` | `FiniteGraphTemporalCurvatureLaw.lean` |
| Pair curvature and adjacency reconstruction | `HTGeometry.finiteGraphPairTemporalCurvature_eq`; `HTGeometry.adj_iff_finiteGraphPairTemporalCurvature_pos` | same |
| Partition curvature, nonnegativity and exact zero classification | `HTGeometry.finiteGraphPartitionTemporalCurvature_eq_rank_sub_blockRankSum`; `HTGeometry.finiteGraphPartitionTemporalCurvature_eq_zero_iff` | same |
| Exact anchored chordal return density and no nonzero exact return | `HTGeometry.anchoredProjectiveReturnFrequency_of_connected`; `HTGeometry.no_nonzeroExactAnchoredReturn_of_connected` | `ConnectedNetworkRecurrenceLaw.lean` |
| Homogeneous path density, extinction, Hilbert-dimension rate and site double-log rate | `HTGeometry.thermodynamicProjectiveRecurrenceExtinctionLaw` | `ThermodynamicProjectiveRecurrenceExtinctionLaw.lean` |
| One countable-network exhaustion: residual/dense event, probability-one event and rank divergence | `HTGeometry.infiniteNetworkExhaustion_temporalRank_tendsto_atTop` with `networkExhaustionGoodSet_residual` and `measure_compl_networkExhaustionGoodSet_eq_zero` | `InfiniteNetworkExhaustion.lean` |
| Static onsite-plus-nearest-neighbour qudit paths attain every positive-weight replica floor simultaneously | `HTGeometry.exists_quditPath_generic_survivalFidelityFloor` | `GenericLocalCollisionExtremality.lean` |
| Component histogram collision identity | `HTGeometry.fidelityReplicaCollisionMass_factorizedOn_eq_componentCollisionMass` | `ComponentReplicaCollisionLaw.lean` |
| Uniform component SFF product and moment limit | `HTGeometry.card_pow_mul_componentCollisionMass_eq_prod`; `HTGeometry.tendsto_componentFormFactorMoment` | `ComponentSpectralFormFactorProduct.lean` |
| Fixed-component product of independent unit exponentials | `HTGeometry.tendsto_prod_replicaFormFactorCoeff`; `HTGeometry.tendsto_sffLaw_unitExpLaw` | `ComponentFormFactorExponentialLimit.lean`; `SpectralFormFactorExponentialLimit.lean` |

## Countable completion

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| Trivial relation lattice, full countable hull, dense every future tail, zero-only exact return, exact liminf/limsup, syndetic near-level and exact interior crossings | `HTGeometry.completeSaturatedProjectiveRecurrenceLaw` | `CountableProjectiveFutureUniversalityLaw.lean` |
| Arbitrarily small domain-preserving self-adjoint Schatten-1 diagonal perturbation, unbounded finite-window rank and all complete recurrence conclusions | `HTGeometry.exists_arbitrarilyWeak_completeProjectiveRecurrenceLaw` | same |
| One separable trace-class interaction direction; countable exceptional couplings; complete recurrence outside it | `HTGeometry.exists_arbitrarilyWeak_separable_completeProjectiveRecurrenceRayLaw` | `SeparableInteractionRecurrenceRayLaw.lean` |
| Diameter-scaled countable l-bit field: absolute summability, uniform finite-window thermodynamic convergence, exact jet dimension and one reporter at every birth order | `HTGeometry.thermodynamicDiameterLBitCascadeLaw` | `ThermodynamicDiameterLBitCascadeLaw.lean` |
| Same diameter-scaled field gives bounded self-adjoint multiplication Hamiltonian and strongly continuous unitary `L²` dynamics for every Borel measure | `HTGeometry.thermodynamicDiameterLBitHilbertDynamicsLaw` | `ThermodynamicDiameterLBitHilbertDynamicsLaw.lean` |
| Same unscaled infinite field: maximal local-flip rank in every finite environment and volume-independent exponential commutator bound | `HTGeometry.quasiLocalInfiniteLBit_fullRank_and_commutatorBound` | `InfiniteLBitRecurrenceLocalitySeparationLaw.lean` |

## Law III: measurement quotient, target capacity and complexity applications

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| Reverse-water objective, two-sided logarithmic deadline and post-delay syndetic return | `RHTower.universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich` | `ProjectiveGaussianRateDistortion.lean` |
| Observer edge-phase energy, graph zero set and capacity `D-c` | `RHTower.finite_quantum_observer_coherence_law` | `FiniteQuantumObserverCoherenceLaw.lean` |
| Observer recurrence deadline and displacement bound | `RHTower.exists_finiteQuantumObserver_graphRank_distance_recurrence` | `FiniteQuantumObserverGraphRecurrenceBound.lean` |
| Exact observer displacement identity and global two-sided equivalence with component-root chord energy | `RHTower.finiteQuantumObserverDistanceSq_eq_phaseEnergy`; `RHTower.observerPhaseEnergy_rootChordEnergy_comparable` | `FiniteQuantumObserverCoherenceLaw.lean`; `FiniteQuantumObserverGraphMetricEquivalence.lean` |
| Exact observer first-return exponent `(r-1)/2` for visible rank `r≥2`, plus unconditional exponent-zero boundary ranks `r=0,1` | `RHTower.tendsto_log_finiteQuantumObserverReturnTime_of_graphNonVWA`; `RHTower.tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_zero`; `RHTower.tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_one` | `FiniteQuantumObserverFirstReturnExponentLaw.lean`; `FiniteQuantumObserverGraphExtremalityLaw.lean` |
| One conull set on full simple-spectrum locus of every real-linear Hermitian family escaping balanced real spectral relations satisfies exact exponent `max(r-1,0)/2` simultaneously for every finite observer chosen afterward | `RHTower.ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus`; supporting `HTGeometry.volume_vwa_sortedEdgeGapRatio_eq_zero`; `RHTower.ae_all_observerGraphGapRatio_not_vwa_simpleLocus` | `LinearSpectralGapRatioExtremality.lean`; `FiniteQuantumObserverGraphExtremalityLaw.lean` |
| Unconditional static-local same-Hamiltonian capstone: for every path length `L≥8194`, one self-adjoint simple-spectrum onsite-plus-nearest-neighbour Hamiltonian on `2L` qubits has universal all-observer exponent and certified operator-norm two-gate lower ramp throughout explicit laboratory window | `RHTower.exists_nearestNeighborPath_growth_universalObserverLaw_of_length`; shifted premise-free form `RHTower.universalNearestNeighborPath_growth_universalObserverLaw` | `StaticLocalUniversalObserverRecurrenceLaw.lean` |
| Arbitrary finite Hermitian Hamiltonian and physical density/effect family: same Born record either never exits or returns strictly after a witnessed exit, before least graph--resolution certified deadline | `RHTower.finiteHermitianBorn_positiveTarget_optimal_neverExits_or_postExit` | `FiniteHermitianBornPostExitRecurrenceLaw.lean` |
| Unitary evolution preserves density matrices and trace-expectation displacement equals absolute Born-probability displacement | `RHTower.finiteHermitianEvolvedDensityMatrix`; `RHTower.finiteHermitian_traceExpectationNorm_eq_bornAbs`; `RHTower.finiteHermitianBornTotalDeviation_eq_expectation` | `FiniteHermitianBornPostExitRecurrenceLaw.lean` |
| Generic connected graph-local upper completed-time Choi-target occupation and explicit padded-word union bound | `RHTower.connectedNetwork_completedTime_paddedCircuitTargets_generic` | `ConnectedNetworkStaticChoiComplexityPlateauLaw.lean` |
| Same bounded-weight Pauli Hamiltonian: syndetic return-hard-return and permanent two-query separation from Haar benchmark | `RHTower.pauliBounded_complexityAlternation_and_permanentHaarSeparation` | `StaticQLocalComplexityHaarSeparationLaw.lean` |
| Prime hard polygon, terminal return and permanent separator | `RHTower.pauliBounded_completeCircuitPolygon_and_permanentHaarSeparation` | `PauliLocalPrimeTorsionCircuitPolygonLaw.lean` |
| Robust two-sided complexity reflection and exact-return palindrome | `RHTower.choiComplexity_reflect`; `RHTower.choiComplexity_reflect'`; `RHTower.choiComplexity_eq_of_exact_return` | `AutonomousReturnReflection.lean` |
| Nested inverse-power path: exact finite restriction, energy in `[0,3]`, uniform tail `L⁻¹+L⁻³`, thermodynamic convergence | `StaticLocalLaboratoryComplexityGrowthLaw.nestedFiniteEnergy_restriction`; `nestedInfiniteEnergy_nonneg_le_three`; `nestedInfiniteEnergy_uniform_tail`; `nestedTruncatedEnergy_tendsto` | `StaticLocalNestedThermodynamicRampReturnLaw.lean` |
| Same explicit nested static nearest-neighbour path: finite-time linear operator-complexity envelope, factorial-four exact return and exact reflected bounds; one complete capstone conjoins these with thermodynamic clauses | `StaticLocalLaboratoryComplexityGrowthLaw.nestedInversePowerChain_floor_linear_growth`; `nestedInversePowerChain_exact_return`; `nestedOperatorTwoGateComplexity_exact_return_reflect`; `nestedStaticLocal_thermodynamic_ramp_return_reflection`; `nestedStaticLocal_complete_thermodynamic_ramp_return_reflection` | `StaticLocalNestedThermodynamicRampReturnLaw.lean` |
| Arbitrary tree phase-tail obstruction against arbitrary nonlocal and non-diagonal support-certified one/two-qubit circuits | `StaticLocalLaboratoryComplexityGrowthLaw.treePhase_twoGateCount_gt`; cut core `exists_tree_cut_separating_circuit` | `TreePhaseTailCapacityLower.lean`; `CircuitTreeCutCertificate.lean` |
| Free scalar/one-qubit centering of omitted controlled phases and exact residual identity | `StaticLocalLaboratoryComplexityGrowthLaw.centeredPairCircuit_matrix`; `centeredPairCircuit_twoGateCount`; `p11_centered_residual` | `CenteredControlledPhaseGate.lean` |
| Concrete nearby-time failure of all-pairs monotonicity inside nested laboratory window: early complexity at least `1514`, late complexity at most `1513`, strict reversal and `not MonotoneOn` | `monotonicityCounterEarly_complexity_lower`; `monotonicityCounterLate_complexity_upper`; `counterLateCircuit_approximates`; `monotonicityCounter_strict_complexity_reversal`; `nestedOperatorTwoGateComplexity_not_monotoneOn_laboratoryWindow` | `NestedMonotonicityLower.lean`; `NestedMonotonicityUpper.lean`; `NestedMonotonicityCounterexample.lean` |
| One countable static nearest-neighbour Pauli field, selected once, with absolutely summable coefficients; every finite prefix maximally projective and syndetically recurrent; paired-prefix laboratory ramp; eventually near-Hilbert continuous-circuit excursion and consecutive re-entry; bounded self-adjoint UHF Hamiltonian and point-norm continuous automorphism group; literal-prefix Hamiltonian convergence and compact-time Schrödinger/Heisenberg convergence | `HTGeometry.exists_thermodynamicSameFieldLifecycle` | `ThermodynamicSameFieldUHFRecurrenceComplexityLaw.lean` |
| Complete phase-saturated continuous `SU(4)` two-qubit circuit image: completed-time operator-norm occupation bound for every maximally projective spectrum; near-Hilbert budget `2^n/[64(n+1)]` has vanishing entropy-times-volume envelope; exact equivalence with physical Schrödinger approximation on every literal prefix; unconditional one-field capstone | `HTGeometry.maximallyProjective_continuousCircuitCapture_completedTime_le`; `HTGeometry.tendsto_nearHilbertContinuousCircuitOccupationCost_atTop`; `RHTower.thermodynamicLiteralPrefixContinuousCircuitCaptureTarget_physical_iff`; `RHTower.ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_continuousCircuitOccupation`; `RHTower.exists_thermodynamicSameFieldContinuousCircuitOccupationLaw` | `ContinuousCircuitCompletedOccupationLaw.lean`; `ThermodynamicSameFieldContinuousCircuitOccupationLaw.lean` |
| Arbitrary-spectrum finite-aperture continuous-circuit occupation: for every finite spectrum, including degeneracies and exact resonances, every translated window and complete arbitrary-`SU(4)` two-qubit circuit family at operator tolerance `1/20` obey explicit Fejér envelope. Exact zero-action packet sheets persist; all nonzero sheets receive `2/(T Δ_N^nz)` correction with unconditional `Δ_N^nz>0`. No spectral premise. Maximal-projective specialization recovers previous law; same static nearest-neighbour field satisfies it at every literal prefix and resolution/window. | `HTGeometry.finitePacketNonzeroDetuningFloor_pos`; `HTGeometry.resonantPacketIndexSet_card_add_nonresonantPacketIndexSet_card`; `HTGeometry.arbitrarySpectrum_periodicProductFejerMajorant_windowMean_le`; `HTGeometry.arbitrarySpectrum_finiteCubeVisit_tensorMajorantWindowUpper`; `HTGeometry.arbitrarySpectrum_continuousCircuitCapture_finiteWindow_le`; `RHTower.ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_continuousCircuitFiniteWindow`; `RHTower.exists_thermodynamicSameFieldFiniteWindowContinuousCircuitOccupationLaw` | `ArbitrarySpectrumFiniteDetuningTensorWindowLaw.lean`; `ArbitrarySpectrumFiniteWindowContinuousCircuitOccupationLaw.lean`; `ThermodynamicSameFieldFiniteWindowContinuousCircuitOccupationLaw.lean` |
| Static-local exponential continuous-circuit plateau: for every sufficiently large `L`, one ordinary time-independent nearest-neighbour Hamiltonian on `2L` qubits lies in controlled inverse-square ball, has quantitative laboratory ramp, consecutive near-Hilbert continuous-circuit exits and re-entries, exponentially wide `2^(L/2)` pointwise hard plateaux at projective error `1/40` and half near-Hilbert budget, linear norm cap, and permanent local non-Haar two-query signal | `RHTower.eventually_exists_nearestNeighborPath_exponentialContinuousCircuitPlateau_capstone`; predicates `RHTower.NearestNeighborLaboratoryRamp`, `RHTower.NearestNeighborNearHilbertContinuousFirstReturn`, `RHTower.NearestNeighborNearHilbertExponentialHardPlateaux` | `NearestNeighborExponentialContinuousCircuitPlateauCapstone.lean` |
| Quantitative first-principles bridge behind hard plateaux: explicit Lie-product remainder; projective Pauli-two-local `SU(4)` compiler with error `3 m^3 ‖H‖² |t|²/r` and exactly `rm` gates; autonomous projective backward cone; exponential width/cost arithmetic fitting compiler below half near-Hilbert budget | `HTGeometry.norm_list_exp_product_pow_sub_exp_sum_le`; `HTGeometry.exists_twoLocal_projectiveTrotterCircuit_normBound`; `HTGeometry.twoLocal_projectiveCircuitHard_backwardInterval`; `HTGeometry.eventually_two_mul_continuousCircuitPlateauCompilerCost_le_nearHilbert`; `HTGeometry.continuousCircuitPlateau_compiler_small`; `HTGeometry.continuousCircuitPlateau_compiler_error` | `QuantitativeLieProductFormula.lean`; `TwoLocalProjectiveTrotterCompilerLaw.lean`; `ProjectiveContinuousCircuitConeLaw.lean`; `ContinuousCircuitExponentialPlateauBudgetLaw.lean` |
| Physical path data for plateau: site relabelling preserves onsite-plus-edge locality and Pauli weight at most two; selected numbered-register Hamiltonian has norm at most `L+2` and lies within `1/L` of explicit inverse-square seed | `HTGeometry.hasPauliWeightAtMost_two_reindex_of_mem_siteFactorLocalSubmodule`; `RHTower.pairQubitProjectivePauliSeed_hasPauliWeightAtMost_two`; `RHTower.norm_pairQubitProjectivePauliSeed_le_length_add_two`; `RHTower.norm_pairQubitProjectivePauliSeed_sub_inverseSquare_le_inv_length` | `SiteFactorLocalReindexLaw.lean`; `PairQubitProjectiveSeedLocalCompilerData.lean` |
| Same one-field recurrence-desert lifecycle plus, simultaneously for every fixed finite alphabet, polynomial exponent and target family, upper completed-time padded-circuit Choi occupation bounded by an explicit envelope tending to zero along paired literal prefixes | `RHTower.ThermodynamicSameFieldLifecycle.thermodynamicPairedPrefix_polynomialCircuitPlateau`; `RHTower.tendsto_thermodynamicPairedPrefixPolynomialCircuitCost_atTop`; `RHTower.exists_thermodynamicSameFieldPolynomialCircuitPlateauLaw` | `ThermodynamicSameFieldPolynomialCircuitPlateauLaw.lean` |
| Every finite maximally projective Hamiltonian has projective operator-norm returns in every interval of one fixed finite length at every positive resolution; specialization to every literal selected path prefix | `HTGeometry.maximallyProjective_unitaryEvolution_projectiveReturn_syndetic`; `HTGeometry.infinitePathPrefix_projectiveReturn_syndetic` | `ThermodynamicSameFieldUHFRecurrenceComplexityLaw.lean` |
| Arbitrary scalar-unitary approximation controls anchored relative-phase return within twice radius; exact completed anchored occupation plus orbit speed forces arbitrarily late continuous projective-return deserts | `HTGeometry.norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar`; `HTGeometry.limsup_windowProbability_projectiveReturnTimes_le`; `HTGeometry.maximallyProjective_scalarUnitaryReturnTimes_late_deserts` | `ThermodynamicProjectiveRecurrenceDesertLaw.lean` |
| Same countable local Pauli field has explicit inverse-occupation desert width `delta/(2 beta_n)-delta` tending to infinity; all sufficiently large prefixes realize such desert after every epoch; closedness plus syndetic recurrence enclose every desert between actual consecutive projective returns separated by at least that width; every prescribed gap occurs eventually, so no volume-independent projective-recurrence clock survives | `HTGeometry.thermodynamicProjectiveDesertWidth_tendsto_atTop`; `HTGeometry.infinitePathPrefix_quantitativeProjectiveRecurrenceDeserts`; `HTGeometry.scalarUnitaryReturnTimes_consecutiveVisitGap`; `HTGeometry.ThermodynamicRecurrenceDesertLifecycle.eventually_quantitativeConsecutiveProjectiveReturnGaps`; `HTGeometry.exists_thermodynamicConsecutiveProjectiveReturnGapLaw`; `HTGeometry.ThermodynamicRecurrenceDesertLifecycle.eventually_arbitraryWidthProjectiveDeserts` | `ThermodynamicProjectiveRecurrenceDesertLaw.lean` |
| Exact UHF support: coherent local Pauli embeddings, absolutely summable bounded self-adjoint generator, continuous unitary group and point-norm automorphism group | `HTGeometry.infinitePathUHFHamiltonian`; `HTGeometry.isSelfAdjoint_infinitePathUHFHamiltonian`; `HTGeometry.infinitePathUHFDynamics`; `HTGeometry.continuous_infinitePathUHFDynamics_apply`; `HTGeometry.infinitePathUHFDynamics_add_apply` | `QubitUHFLocalPauli.lean`; `ThermodynamicPathUHFDynamics.lean` |
| Literal finite-prefix partial-sum identity, norm convergence of generators and uniform-on-compact Schrödinger and Heisenberg convergence | `HTGeometry.embeddedInfinitePathPrefixHamiltonian_eq_sum`; `HTGeometry.tendsto_embeddedInfinitePathPrefixHamiltonian`; `HTGeometry.embeddedInfinitePathPrefixEvolution_uniformOnCompact`; `HTGeometry.embeddedInfinitePathPrefixHeisenberg_uniformOnCompact` | `ThermodynamicPathUHFPrefixConvergence.lean` |

## Law IV: inference boundary

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| Every bounded-time operator-norm tube around every finite Hermitian Hamiltonian of dimension at least three contains commuting simple-spectrum periodic and maximal-return-exponent Hamiltonians with one common eigenbasis; same normalized cyclic state has physical survival-fidelity first-return exponents `0` and `(D-2)/2` | `HTGeometry.exists_sameEigenbasis_periodic_and_maximalPhysicalReturn_uniform_horizon` | `PhysicalFirstReturnHorizonInstabilityLaw.lean` |
| One fixed spectrum/protocol/earlier record with every future probability, Jacobi endpoint classification and free-fermion all-sector lift | `RHTower.ParityForecast.one_fixed_nearestNeighbor_freeFermion_every_future_probability` | `FermionicFockIsospectrality.lean` |
| Minimax terminal absolute error `1/2` | `RHTower.ParityForecast.every_forecaster_has_half_error` | `ParityConditionedForecastingInstability.lean` |
| Complete polynomial cyclic-local data do not universally decide persistent recurrence | `RHTower.universalQuantumRecurrenceAnatomyLaw`, field `localDataDoNotDecide` | `UniversalQuantumRecurrenceAnatomyLaw.lean` |
| Complete perturbative bounded-observable and SFF jets do not decide nonperturbative completion | `RHTower.perturbativeBoundedSpectralObservableJet_everyCompletion_eq`; `RHTower.perturbativeSpectralFormFactorJet_compactFamilies_eq` and packaged capstone | `NonperturbativeQuantumRecurrenceSeparationLaw.lean`; `UniversalQuantumRecurrenceAnatomyLaw.lean` |
| Compact exact moments determine spectrum and recurrence plateau | `RHTower.compactExactMoments_determine_spectrum`; `RHTower.compactExactMoments_determine_recurrencePlateau` | `QuantumRecurrenceGlobalCompletionLaw.lean` |

## Included prior-results appendix

Single compiled document includes
`../persistent-phase-geometry-quantum-recurrence/appendices.tex`. Every result
there is dependency-closed by that manuscript's
`../persistent-phase-geometry-quantum-recurrence/claim-trace.md`, including
finite contractions, arbitrary spectral types, projective completion,
replica-grid readout, coupling walls, static path recurrence, reverse-water
geometry, observer bounds and finite-record inference. This ledger supersedes
old paper-only status labels: only rows backed by checked declarations are
retained in present main text.

## Experimental section boundary

Section `Experimental tests and falsification targets` introduces no new
mathematical theorem. Exact predictions in its nine protocols refer back to
already traced declarations: full-process horizon instability, bound-state support edge, nine-level
scalar/resolved witness, finite-observer graph law, generic subsystem
rank/curvature and exact density, universal observer-rank first-return sweep,
all-state support-stratified physical
local-path first-return exponent and vanishing-tail resolution singularity,
finite-aperture spectroscopic circuit occupation, static-local exponential
plateau, and nested path ramp/return/reflection. Conditional same-field protocol uses only
already-traced finite-prefix return-gap and continuous-circuit occupation
bounds.  Statements about calibration, randomized measurements, finite
sampling, compiler searches and falsification are experimental proposals, not
deductions of device fidelity or infinite-limit validation.  Circuit witnesses
certify capture; compiler failure alone does not certify hardness.

## Axiom and source audit

`/tmp/QuantumRecurrencePaperAudit.lean` and
`/tmp/AuditNestedMonotonicity.lean` import load-bearing modules and run
`#print axioms` on headline declarations. Audit passed: every reported
kernel dependency is among `[propext, Classical.choice, Quot.sound]`.
Targeted 17 August audits of
`FiniteHermitianBornPostExitRecurrenceLaw`,
`ThermodynamicDiameterLBitCascadeLaw` and
`ThermodynamicDiameterLBitHilbertDynamicsLaw` report same standard
dependencies.
Targeted 27 August audits of
`quantumRecurrence_scalarResolved_strictSeparation` and
`universalQuantumRecurrenceInformationHierarchyLaw` also report only
`[propext, Classical.choice, Quot.sound]`; both source checks and targeted
module builds passed.
Targeted 27 August source checks and build of
`ThermodynamicSameFieldUHFRecurrenceComplexityLaw` passed.  Axiom audit of
same-field capstone, recurrence theorem, UHF generator, literal-prefix
identity and both compact-time convergence laws reports only
`[propext, Classical.choice, Quot.sound]`.
Targeted 27 August source check and module build of
`ThermodynamicProjectiveRecurrenceDesertLaw` passed.  Axiom audit of spectral
anchoring, finite-system hard-gap law, divergent desert scale, closed-return
consecutive-gap extraction and unconditional same-field capstones reports only
`[propext, Classical.choice, Quot.sound]`.
Targeted 27 August source check and module build of
`ThermodynamicSameFieldPolynomialCircuitPlateauLaw` passed.  Axiom audit of
paired-prefix dimension, maximal projectivity, exact completed-time/Haar
bound, vanishing entropy envelope and unconditional one-field capstone reports
only `[propext, Classical.choice, Quot.sound]`.
Targeted 27 August source checks and module build of
`ContinuousCircuitCompletedOccupationLaw` and
`ThermodynamicSameFieldContinuousCircuitOccupationLaw` passed.  Axiom audit
of generic completed-time bound, near-Hilbert decay, exact physical bridge,
literal-prefix occupation theorem and unconditional one-field capstone reports
only `[propext, Classical.choice, Quot.sound]`.
Targeted 28 August build of
`ThermodynamicSameFieldFiniteWindowContinuousCircuitOccupationLaw` passed.
Axiom audit of finite-packet detuning positivity, finite-cube window law,
continuous-circuit finite-window capstone and unconditional same-field
capstone reports only `[propext, Classical.choice, Quot.sound]`.  Four new
modules contain no forbidden declaration; repository lint reports only
unrelated pre-existing umbrella-reachability failures, and all four modules
are reachable from their theorem-area umbrellas.
Targeted 28 August builds of
`ArbitrarySpectrumFiniteDetuningTensorWindowLaw` and
`ArbitrarySpectrumFiniteWindowContinuousCircuitOccupationLaw` passed.
Axiom audit of unconditional nonzero-floor positivity, arbitrary-spectrum
Fejér mean, arbitrary-spectrum finite-cube visit and physical
continuous-circuit capstone reports only
`[propext, Classical.choice, Quot.sound]`. Both new modules contain no
forbidden declaration and are reachable from `HTGeometry` umbrella; umbrella
itself was not built.
Targeted 28 August checks and builds of
`QuantitativeLieProductFormula`, `TwoLocalProjectiveTrotterCompilerLaw`,
`ProjectiveContinuousCircuitConeLaw`,
`ContinuousCircuitExponentialPlateauBudgetLaw`,
`PairQubitProjectiveSeedLocalCompilerData` and
`NearestNeighborExponentialContinuousCircuitPlateauCapstone` passed without
errors in these modules; no full umbrella build was run.  Axiom audit of
product-formula bound, compiler, backward cone, budget separation, locality
transport and capstone reports only
`[propext, Classical.choice, Quot.sound]`.
Targeted 28 August source check and module build of
`QuditPathPhysicalRecurrenceCollisionLaw` passed.  Axiom audit of generic
spectral-escape bridge, conventional local-path theorem and closed shifted
capstone reports only `[propext, Classical.choice, Quot.sound]`.
Targeted 28 August source check and module build of
`PhysicalFirstReturnHorizonInstabilityLaw` passed.  Axiom audit of its
same-eigenbasis capstone, exact-period exponent-zero bridge and dense
non-VWA-spectrum selection reports only
`[propext, Classical.choice, Quot.sound]`; module is wired into HTGeometry
umbrella and no umbrella build was run.
Targeted 28 August source check and module build of
`AllStateSpectralSupportRecurrenceLaw` passed.  Axiom audit of support-card
compression, simultaneous chartwise all-state exponent theorem and
unconditional local capstone reports only
`[propext, Classical.choice, Quot.sound]`; module is wired into HTGeometry
umbrella and no umbrella build was run.
Targeted 28 August source check and module build of
`VanishingTailRecurrenceExponentInstabilityLaw` passed.  Its source contains
no forbidden declaration.  Axiom audit of uniform all-time deficit, exact
coarse cutoff, physical maximal exponent, simultaneous chartwise theorem and
unconditional local capstones reports only
`[propext, Classical.choice, Quot.sound]`; module is wired into HTGeometry
umbrella and no umbrella build was run.
Targeted 28 August build of
`StaticLocalUniversalObserverRecurrenceLaw` passed.  Axiom audit of global
linear gap-frame extremality, simultaneous full-simple-locus all-observer law,
premise-free shifted local capstone and conventional `L≥8194` local capstone
reports only `[propext, Classical.choice, Quot.sound]`.  New observer modules
contain no `sorry`, `admit`, project `axiom`, `opaque` or `unsafe`
declaration and are wired into theorem-area umbrellas; neither umbrella was
built.
Repository formal lint forbids `sorry`, `admit`, project `axiom`,
`opaque` and `unsafe` declarations.

## Explicit exclusions

- No first-return time from initial epoch is inferred from inverse completed density.  Inverse density supplies a desert width; a separate closedness-and-syndeticity argument proves that width lower-bounds an arbitrarily late actual consecutive-return gap.
- No pointwise monotonicity, maximal-complexity saturation plateau or finite-time random-matrix ramp. New finite-volume theorem does prove pointwise exclusion of a fixed circuit budget across exponential-width intervals; it does not identify constant complexity value, maximal saturation or hardness at every late time. Same-field result combines completed-time occupation extinction with finite-window occupation upper bound; neither is a pointwise lower bound at every late time. Pointwise monotonicity is explicitly false: nested path gives a two-sided linear envelope and scale-separated ordering, but also a strict nearby-time drop inside same laboratory window.
- No Haar randomization by static bounded-local Hamiltonians.
- No bounded-degree geometry claim for bounded-weight all-to-all Pauli terms.
- No infinite-volume orbit recurrence, infinite-system circuit complexity or interchange of size and time limits.
- No translation invariance, explicit numerical witness for existential same-field or per-size plateau selection, or volume-uniform finite-window convergence rate.  Finite packet detuning is positive at each prefix but may shrink with size or resolution.  Rather than assuming a volume-uniform recurrence deadline, same-field theorem proves that none exists at stated projective accuracy.
- No physical-space reconstruction without supplied subsystem factorization.
