# Internal claim ledger

Not part of submitted paper. Audit date: 17 August 2026.

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

## Law III: target capacity and complexity

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
Repository formal lint forbids `sorry`, `admit`, project `axiom`,
`opaque` and `unsafe` declarations.

## Explicit exclusions

- No first-return time inferred from inverse completed density.
- No pointwise monotonicity, saturation plateau or finite-time random-matrix ramp. Pointwise monotonicity is explicitly false: nested path gives a two-sided linear envelope and scale-separated ordering, but also a strict nearby-time drop inside same laboratory window.
- No Haar randomization by static bounded-local Hamiltonians.
- No bounded-degree geometry claim for bounded-weight all-to-all Pauli terms.
- No infinite-volume orbit recurrence, infinite-system circuit complexity or interchange of size and time limits.
- No physical-space reconstruction without supplied subsystem factorization.

