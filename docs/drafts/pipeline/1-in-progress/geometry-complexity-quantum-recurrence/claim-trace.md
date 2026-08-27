# Internal claim ledger

Not part of submitted paper. Audit date: 27 August 2026.

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
| Projective characters, detuning, relation lattice, temporal rank, hull dimension, character constancy, replica height, `tau+rho=D-1` | `HTGeometry.finiteProjectiveRecurrence_universalLaw` | `UniversalProjectiveRecurrenceCapstoneLaw.lean` |
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
| Countable pure-point recurrence | `RHTower.exists_summablePhaseEnergy_recurrence` | `SummablePurePointPhaseRecurrence.lean` |
| Positive exact return iff visible group is cyclic | `RHTower.exists_positive_unitFidelity_iff_cyclic` | `ObserverTemporalUniversalityLaw.lean` |
| Atomless continuum dimension and vanishing fixed return-window density | `RHTower.atomlessProjectiveObserverTemporalPhaseLaw`; packaged in `RHTower.universalQuantumRecurrenceAnatomyLaw` | `ObserverTemporalUniversalityLaw.lean`; `UniversalQuantumRecurrenceAnatomyLaw.lean` |

## Law II: local networks, thermodynamics and replicas

| Paper block | Checked declaration(s) | Source |
|---|---|---|
| One dense, residual, full-measure coefficient set works for every induced subsystem | `HTGeometry.allSubsystemGenericSet_dense_residual_fullMeasure` | `SubsystemComponentWitness.lean` |
| Exact subsystem component formula and connected rank `D-1` | `HTGeometry.anchoredTemporalRank_subsystemHamiltonian_of_generic`; `HTGeometry.finiteGraphTemporalRank_add_one_of_connected` | `SubsystemComponentWitness.lean`; `FiniteGraphTemporalCurvatureLaw.lean` |
| One conull set in every open simple-spectrum qudit-path chart simultaneously has maximal projectivity, stroboscopic exponent `D-1`, first-gap-clock exponent `D-2`, every positive-weight replica floor and zero-only exact anchored return | `HTGeometry.exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw` | `QuditPathRecurrenceCollisionCapstone.lean` |
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
| Every finite maximally projective Hamiltonian has projective operator-norm returns in every interval of one fixed finite length at every positive resolution; specialization to every literal selected path prefix | `HTGeometry.maximallyProjective_unitaryEvolution_projectiveReturn_syndetic`; `HTGeometry.infinitePathPrefix_projectiveReturn_syndetic` | `ThermodynamicSameFieldUHFRecurrenceComplexityLaw.lean` |
| Arbitrary scalar-unitary approximation controls anchored relative-phase return within twice radius; exact completed anchored occupation plus orbit speed forces arbitrarily late continuous projective-return deserts | `HTGeometry.norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar`; `HTGeometry.limsup_windowProbability_projectiveReturnTimes_le`; `HTGeometry.maximallyProjective_scalarUnitaryReturnTimes_late_deserts` | `ThermodynamicProjectiveRecurrenceDesertLaw.lean` |
| Same countable local Pauli field has explicit inverse-occupation desert width `delta/(2 beta_n)-delta` tending to infinity; all sufficiently large prefixes realize such desert after every epoch; closedness plus syndetic recurrence enclose every desert between actual consecutive projective returns separated by at least that width; every prescribed gap occurs eventually, so no volume-independent projective-recurrence clock survives | `HTGeometry.thermodynamicProjectiveDesertWidth_tendsto_atTop`; `HTGeometry.infinitePathPrefix_quantitativeProjectiveRecurrenceDeserts`; `HTGeometry.scalarUnitaryReturnTimes_consecutiveVisitGap`; `HTGeometry.ThermodynamicRecurrenceDesertLifecycle.eventually_quantitativeConsecutiveProjectiveReturnGaps`; `HTGeometry.exists_thermodynamicConsecutiveProjectiveReturnGapLaw`; `HTGeometry.ThermodynamicRecurrenceDesertLifecycle.eventually_arbitraryWidthProjectiveDeserts` | `ThermodynamicProjectiveRecurrenceDesertLaw.lean` |
| Exact UHF support: coherent local Pauli embeddings, absolutely summable bounded self-adjoint generator, continuous unitary group and point-norm automorphism group | `HTGeometry.infinitePathUHFHamiltonian`; `HTGeometry.isSelfAdjoint_infinitePathUHFHamiltonian`; `HTGeometry.infinitePathUHFDynamics`; `HTGeometry.continuous_infinitePathUHFDynamics_apply`; `HTGeometry.infinitePathUHFDynamics_add_apply` | `QubitUHFLocalPauli.lean`; `ThermodynamicPathUHFDynamics.lean` |
| Literal finite-prefix partial-sum identity, norm convergence of generators and uniform-on-compact Schrödinger and Heisenberg convergence | `HTGeometry.embeddedInfinitePathPrefixHamiltonian_eq_sum`; `HTGeometry.tendsto_embeddedInfinitePathPrefixHamiltonian`; `HTGeometry.embeddedInfinitePathPrefixEvolution_uniformOnCompact`; `HTGeometry.embeddedInfinitePathPrefixHeisenberg_uniformOnCompact` | `ThermodynamicPathUHFPrefixConvergence.lean` |

## Law IV: inference boundary

| Paper block | Checked declaration(s) | Source |
|---|---|---|
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
mathematical theorem. Exact predictions in its four protocols refer back to
already traced declarations: the nine-level scalar/resolved witness,
finite-observer graph law, generic subsystem rank/curvature and exact density,
and nested path ramp/return/reflection. Statements about calibration,
randomized measurements, finite sampling and falsification are explicitly
experimental proposals, not deductions of device fidelity or infinite-limit
validation.

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
Repository formal lint forbids `sorry`, `admit`, project `axiom`,
`opaque` and `unsafe` declarations.

## Explicit exclusions

- No first-return time from initial epoch is inferred from inverse completed density.  Inverse density supplies a desert width; a separate closedness-and-syndeticity argument proves that width lower-bounds an arbitrarily late actual consecutive-return gap.
- No pointwise monotonicity, saturation plateau or finite-time random-matrix ramp. Pointwise monotonicity is explicitly false: nested path gives a two-sided linear envelope and scale-separated ordering, but also a strict nearby-time drop inside same laboratory window.
- No Haar randomization by static bounded-local Hamiltonians.
- No bounded-degree geometry claim for bounded-weight all-to-all Pauli terms.
- No infinite-volume orbit recurrence, infinite-system circuit complexity or interchange of size and time limits.
- No translation invariance or explicit numerical witness for existential same-field selection.  Rather than assuming a volume-uniform recurrence deadline, same-field theorem proves that none exists at stated projective accuracy.
- No physical-space reconstruction without supplied subsystem factorization.
