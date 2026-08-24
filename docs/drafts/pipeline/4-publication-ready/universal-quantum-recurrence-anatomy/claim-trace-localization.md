# Claim trace: persistent phase geometry of quantum recurrence

Date: 2026-08-24

Scope: internal verification ledger. Publication manuscript must not mention this file, Lean, HGT, or repository terminology.

## Main laws and consequences

| Manuscript claim | Closed declaration | Source |
|---|---|---|
| Anchored/projective temporal rank plus balanced relation rank equals `D - 1` | `anchoredTemporalRank_add_relationRank`; `projectiveTemporalRank_add_relationRank` | `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.lean:122`; `formal/GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean:199` |
| Detuning-map kernel and range descriptions | `projectiveEnergyDetuning_ker_eq_relationSpace`; `projectiveEnergyDetuning_range_eq_anchoredGapSubspace` | `formal/GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean:77`; `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveRecurrenceConservationLaw.lean:87` |
| Dirichlet first-hit upper bound | `firstHit_le` | `formal/GaloisForLFunctions/HTGeometry/SimultaneousDirichlet.lean:167` |
| Non-VWA vector has exact logarithmic first-hit exponent | `tendsto_log_firstHit_div_log` | `formal/GaloisForLFunctions/HTGeometry/FirstHitExponentLaw.lean:213` |
| Finite-window survival-fidelity replica expansion | `finiteSpectralSurvivalFidelity_pow_expansion` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:181` |
| Long-time symmetric moment converges to collision mass | `finiteSpectralSurvivalFidelityMean_tendsto_collisionMass` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:331` |
| All-order collision floor iff maximal projectivity | `all_fidelityReplicaCollisionMass_eq_floor_iff` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:619` |
| All long-time survival moments tend to floor iff maximal projectivity | `all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff` | `formal/GaloisForLFunctions/HTGeometry/ReplicaCollisionExtremality.lean:642` |
| Arbitrary-qudit every-chart same-Hamiltonian capstone | `exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw` | `formal/GaloisForLFunctions/HTGeometry/QuditPathRecurrenceCollisionCapstone.lean:99` |
| Generic maximality from relation-by-relation escape in same coefficient family | `volume_notMaximallyProjective_eq_zero_of_spectrumEscapesRealRelations` | `formal/GaloisForLFunctions/HTGeometry/QuditPathRecurrenceCollisionCapstone.lean:27` |
| Exact anchored chord-return density | `maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency` | `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveReturnDensityLaw.lean:400` |
| No nonzero exact anchored return at three or more levels | `MaximallyProjectiveEnergy.no_nonzeroExactAnchoredReturn` | `formal/GaloisForLFunctions/HTGeometry/AnchoredProjectiveReturnDensityLaw.lean:426` |
| Exact thermodynamic extinction and rate limits | `thermodynamicProjectiveRecurrenceExtinctionLaw`; `neg_log_quditPathProjectiveReturnDensity_eq` | `formal/GaloisForLFunctions/HTGeometry/ThermodynamicProjectiveRecurrenceExtinctionLaw.lean:209`; same file |
| Persistent mass equals peripheral projection and is the exact late-return threshold | `finiteContractionPersistentMass_eq_norm_sq_projection`; `finiteContraction_returnThreshold_dichotomy` | `formal/GaloisForLFunctions/RHTower/DissipativeQuantumReturnInformationTransition.lean:1106,1375` |
| Exact relation lattice determines completed projective phase ensemble | `spectralRelationLattice_eq_iff_phaseEnsemble_eq`; `screwHull_eq_screwAnnihilator` | `formal/GaloisForLFunctions/HTGeometry/ResolvedRecurrenceRelationCompletenessLaw.lean:168`; `formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewHull.lean:310` |
| Weighted projective variance identity | `projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedCoherence.lean` |
| Reverse-water optimizer and two-sided target-information law | `projectiveCanonicalWaterEntropy_isGaussianRateDistortionMinimum`; `canonicalWaterEntropy_targetInformation_sandwich` | `formal/GaloisForLFunctions/RHTower/ProjectiveGaussianRateDistortion.lean`; `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedTargetVolumeLower.lean:546` |
| Two-sided universal deadline and return after every delay | `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich`; `exists_weightedFloquetFidelity_recurrence_after` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedFloquetRecurrence.lean` |
| Finite-horizon Haar hit union bound | `measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedHaarQuantileActiveSupport.lean:91` |
| Observer displacement identity, zero law, and exact graph capacity | `finite_quantum_observer_coherence_law`; `finiteObserverCoherenceGraph_phaseCapacity` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverCoherenceLaw.lean:217,253` |
| Graph-rank recurrence deadline and matching hard exponent | `exists_finiteQuantumObserver_graphRank_distance_recurrence`; `exists_rankSharp_uniformPureObserver_avoiding_return_until`; `exists_uniformPureObserver_rank_recurrence` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverGraphRecurrenceBound.lean`; `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverGraphSharpness.lean:190,221` |
| Arbitrarily close maximally projective l-bit packet | `exists_lbitEnergy_maximal_uniformly_close` | `formal/GaloisForLFunctions/HTGeometry/LBitTemporalDimensionLaw.lean:481` |
| Finite-horizon Heisenberg perturbation bound | `selfAdjoint_heisenbergEvolution_norm_sub_le` | `formal/GaloisForLFunctions/HTGeometry/FiniteHorizonCStarPerturbationLaw.lean:313` |
| Countable balanced relation hull, covering-number first return, and return after every checkpoint | `mem_anchoredScrewRelationLattice_iff_balancedRelation`; `exists_countableSpectralProjectiveRelationLatticeFirstReturnBound`; `exists_countableSpectralDepth_postCheckpointReturn` | `formal/GaloisForLFunctions/RHTower/CountableSpectralProjectiveRelationMetricEntropyLaw.lean:107,251`; `formal/GaloisForLFunctions/RHTower/CountableSpectralDepthPostExitLaw.lean:23` |
| Exact l-bit coefficient/gap rank classification and conservation | `lbitTemporalRank_eq`; `lbitTemporalRank_add_relationRank` | `formal/GaloisForLFunctions/HTGeometry/LBitTemporalDimensionLaw.lean:233`; `formal/GaloisForLFunctions/HTGeometry/LBitRecurrenceConstraintLaw.lean:29` |
| Fixed-range commuting l-bit ceiling and sharpness | `lbitTemporalRank_le_geometric_linear`; `lbitTemporalRank_eq_geometricSupports_card` | `formal/GaloisForLFunctions/HTGeometry/LBitGeometricLocalityLaw.lean:85,298` |
| Uniform l-bit product state sees full rank and all-order moment equivalence | `lbitUniformStateVisibleTemporalRank_eq`; `lbitUniformState_all_survivalFidelityMoments_extremal_iff` | `formal/GaloisForLFunctions/HTGeometry/LBitUniformStateRecurrenceLaw.lean:155`; same file |

## Local-escape proof trace

| Manuscript proof claim | Closed declaration | Source |
|---|---|---|
| Leaf-extension slice escapes every nonzero balanced affine real relation | `hermitianLocalExtensionSlice_spectrumEscapesAffineRelations` | `formal/GaloisForLFunctions/HTGeometry/AffineSpectrumRelationEscape.lean:74` |
| Locally constant spectral action has constant coefficient packet when interaction lift is connected | `hermitianLocalExtension_constantAction_coefficients_constant` | `formal/GaloisForLFunctions/HTGeometry/HermitianLocalExtensionRelationEscape.lean:630` |
| Second-order response forces coefficient equality along every detected cross-layer edge | `crossLayer_eq_of_selectedLayerAnalyticBranchConstantAction` | `formal/GaloisForLFunctions/HTGeometry/LocalSelectedLayerSpectralResponse.lean:158` |
| Connected nonbipartite old transition graph gives connected lift for every local alphabet of size at least two | `crossLayerLiftGraph_preconnected_of_two_le_card` | `formal/GaloisForLFunctions/HTGeometry/CrossLayerLiftParityRigidity.lean:173` |
| Coded onsite shift makes product spectrum simple | `exists_codedIntegerLayerShift_injective` | `formal/GaloisForLFunctions/HTGeometry/LeafExtensionSpectrumRealRelationEscape.lean:30` |
| Exact open qudit path local space escapes every affine relation | `exists_quditPathChain_spectrumEscapes` | `formal/GaloisForLFunctions/HTGeometry/QuditPathChainEscape.lean:25` |
| Exact path graph and Hilbert cardinality `q^n` | same theorem, plus `leafGraphExtension_comap_pathGraph` | preceding source; `formal/GaloisForLFunctions/HTGeometry/QuditPathLeafArchitecture.lean` |
| Path witness schedule supplies maximal spectrum and good local probes | `exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure`; leaf-extension constructors | `formal/GaloisForLFunctions/HTGeometry/NearestNeighborQuditPathGenericityLaw.lean:67`; `formal/GaloisForLFunctions/HTGeometry/ArbitraryGraphLocalHamiltonianGenericityLaw.lean` |
| Nonempty simple chart exists from spectral escape | `exists_chart_of_spectrumEscapes` | `formal/GaloisForLFunctions/HTGeometry/QuditPathChainRecurrenceExponent.lean:97` |
| Nondegenerate chart gap maps have almost-everywhere discrete and winding exponent laws | `ae_tendsto_log_firstHit_sortedGap`; `ae_tendsto_log_firstHit_sortedGapRatio` | `formal/GaloisForLFunctions/HTGeometry/SpectralRecurrenceExponentLaw.lean:41,58` |

## Quantifier audit

- Main theorem covers every integer `n,q >= 2`, with `D = q^n >= 4`.
- Coefficient space is exact full Hermitian onsite-plus-nearest-neighbour space. Global scalar direction is included and cancels from balanced relations.
- Every nonempty preconnected open simple-spectrum chart has one conull coefficient set.
- One coefficient draw simultaneously satisfies maximal projectivity, both first-hit limits, all positive weights, all replica orders, all long-time moment limits, and no nonzero exact anchored return.
- Stroboscopic exponent is `D - 1`; winding exponent is first-gap-clock normalized and is `D - 2`.
- No unrestricted continuous-time first-return distribution is claimed.
- Thermodynamic statement completes time at each finite size before size limit.

## Closure audit

- Unified 42-declaration manuscript-spine audit: `lake env lean /tmp/quantum_recurrence_unified_audit.lean` passed.
- The unified audit included persistent-carrier, rank conservation, detuning kernel/range, relation-hull, first-hit, replica, weighted, observer upper and hard lower, finite-horizon, post-checkpoint countable, l-bit, local-path, density, and thermodynamic declarations; every printed axiom set was exactly `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean GaloisForLFunctions/HTGeometry/QuditPathRecurrenceCollisionCapstone.lean`: passed.
- `lake build GaloisForLFunctions.HTGeometry.QuditPathRecurrenceCollisionCapstone`: passed; named target only, no umbrella target.
- Axiom audit for both new capstone declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- New capstone module contains no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration.
- No full umbrella build was run.
