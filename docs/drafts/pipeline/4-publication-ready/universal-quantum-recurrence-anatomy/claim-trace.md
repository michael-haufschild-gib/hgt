# Claim trace — 24 October 2026

This ledger covers canonical main.tex/body.tex only. Names below are exact Lean declarations, not proposed interfaces. Prefix HT means GaloisForLFunctions.HTGeometry; prefix RT means RHTower. Paths are relative to formal/GaloisForLFunctions/.

## Main claims

| Paper statement | Exact declaration | File |
|---|---|---|
| Theorem 1: every connected finite graph, dimensions ≥2, full local coefficient space; one conull event for all matrix observers | HT.connectedGraph_ae_universalObserverFirstReturnLaw | HTGeometry/ConnectedNetworkAllObserverRecurrenceLaw.lean |
| Corollary 2: connected support-contained hypergraphs | HT.connectedHypergraph_ae_universalObserverFirstReturnLaw | Same |
| Corollary 3: normalized pure-state fidelity exponent, exact support including zeros | HT.universalObserver_pureState_fidelityReturn | Same |
| Corollary 3: nuclear/trace-radius exponent | RT.HasUniversalFiniteObserverFirstReturnLaw.singleMatrixNuclear | RHTower/StaticLocalAllObserverFirstReturnLaw.lean |
| Theorem 7: real affine spectral escape, arbitrary connected graph | HT.connectedGraph_spectrumEscapesAffineRelations | HTGeometry/ConnectedGraphSpectralAffineEscape.lean |
| Theorem 7: hypergraph escape | HT.connectedHypergraph_spectrumEscapesAffineRelations | Same |
| Theorem 11: weak stationary limit, exact pure-point scaling, interval support and mass inversion | RT.universalStationarySurvivalRecurrenceLaw | RHTower/UniversalStationaryRecurrenceLaw.lean |
| Theorem 11: support edge belongs to support and is its maximum | RT.universalStationaryRecurrenceNoGapBoundStateMassLaw | RHTower/StationaryRecurrenceSupportIntervalLaw.lean |
| Proposition 12: arbitrary unital complex C*-algebra observable stability | HT.selfAdjoint_heisenbergEvolution_norm_sub_le | HTGeometry/FiniteHorizonCStarPerturbationLaw.lean |

## Mechanisms appearing in the paper proofs

| Paper mechanism | Exact declaration(s) | File |
|---|---|---|
| Matrix displacement equals weighted phase energy | RT.finiteQuantumObserverDistanceSq_eq_phaseEnergy | RHTower/FiniteQuantumObserverCoherenceLaw.lean |
| Capacity equals D minus component count | RT.card_graphNonRoot; RT.finite_quantum_observer_coherence_law | RHTower/FiniteQuantumObserverGraphRecurrenceBound.lean; RHTower/FiniteQuantumObserverCoherenceLaw.lean |
| Lemma 4: global root-chord comparison | RT.observerPhaseEnergy_rootChordEnergy_comparable | RHTower/FiniteQuantumObserverGraphMetricEquivalence.lean |
| Lemma 5: exact exponent for a non-VWA visible clock | RT.tendsto_log_finiteQuantumObserverReturnTime_of_graphNonVWA | RHTower/FiniteQuantumObserverFirstReturnExponentLaw.lean |
| Rank-zero and rank-one boundaries | RT.tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_zero; RT.tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_one | RHTower/FiniteQuantumObserverGraphExtremalityLaw.lean |
| Positive constant tolerance scaling | HT.tendsto_log_returnTime_scaled | HTGeometry/ReturnTimeThresholdComparisonLaw.lean |
| Pure-projector coherence graph/support identity | RT.pureStateObserver_coherenceGraph_eq_localizedSupport; RT.HasUniversalFiniteObserverFirstReturnLaw.pureState | RHTower/StaticLocalAllObserverFirstReturnLaw.lean |
| Pure-projector distance = twice fidelity deficit | RT.pureStateObserver_distanceSq_eq_two_mul_fidelityDeficit | Same |
| Positive/negative phase convention bridge | HT.norm_observerPhaseAmplitude_eq_spectralReturnAmplitude | HTGeometry/ConnectedNetworkAllObserverRecurrenceLaw.lean |
| Lemma 8: real Hermitian constant-action rigidity | HT.hermitianLocalExtension_constantAction_coefficients_constant | HTGeometry/HermitianLocalExtensionRelationEscape.lean |
| Finite permutation avoidance for arbitrary real balanced coefficients and target | HT.exists_hermitianLocalExtension_realRootPacket_affineOrbit_ne_zero | HTGeometry/HermitianLocalExtensionAffineRelationEscape.lean |
| Actual physical leaf slice escapes affine relations | HT.leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations | HTGeometry/LeafExtensionSpectrumRealRelationEscape.lean |
| Physical graph-local transport of that slice | HT.SiteFactorChart.leaf_spectrumEscapesAffineRelations | HTGeometry/ConnectedGraphSpectralAffineEscape.lean |
| Lemma 9: named site-product physical witnesses | HT.exists_siteFactorChart_rootedSpanningTree; HT.exists_siteFactorChart_binarySpanningTree; HT.exists_maximallyProjective_mem_siteFactorLocalSubmodule | HTGeometry/SiteFactorGraphWitness.lean |
| Qubit-edge seed and exact Pauli graph | HT.transitionFamilySupportGraph_twoQubitEndpointTransition; HT.exists_physicallyRealized_twoQubitGraphSeed | HTGeometry/PhysicalTwoQubitGraphSeed.lean |
| Exact old-site response formula | HT.twoStepEndpointPacketResponse_eq | HTGeometry/AllVertexEndpointResponse.lean |
| One simultaneous layer shift for every channel | HT.exists_codedIntegerLayerShift_all_responses_ne_zero | HTGeometry/AllLayerEndpointSimultaneousResponse.lean |
| All old probes and new probe remain good after one physical extension | HT.exists_eventually_allVertexGood_leafExtension_of_isHermitian | HTGeometry/HermitianAllVertexGoodLeafExtension.lean |
| Lemma 10: independent balanced incidence rows | RT.graphRootGapIncidence_linearIndependent | RHTower/FiniteQuantumObserverGraphExtremalityLaw.lean |
| Countable chart cover and simultaneous graph extremality | RT.ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus | Same |
| Coordinate genericity closes simple/maximal/universal events together | HT.ae_simple_maximal_universalObserverLaw; HT.exists_submodule_ae_universalObserverLaw | HTGeometry/ConnectedNetworkAllObserverRecurrenceLaw.lean |
| All stationary moments | RT.stationarySpectralReturnProbabilityMeasure_moment | RHTower/StationaryRecurrenceCompletionLaw.lean |
| Atomless law collapses to zero | RT.stationarySpectralReturnProbabilityMeasure_eq_zero_of_noAtoms | Same |
| Continuous factors do not create convolution atoms | RT.conv_singleton_eq_of_samePointMasses | RHTower/StationaryRecurrencePointSpectrumLaw.lean |
| Exact normalized pure-point scaling | RT.stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum | RHTower/StationaryRecurrencePointSpectrumScalingLaw.lean |
| Connected support for every spectral measure | RT.exists_stationarySpectralReturnProbabilityMeasure_support_Icc | RHTower/StationaryRecurrenceSupportIntervalLaw.lean |
| Compact-support continuous pushforward support | RT.support_map_eq_image_support_of_continuous_of_compact | Same |
| Unitary Duhamel inequality | HT.selfAdjoint_unitaryEvolution_norm_sub_le | HTGeometry/FiniteHorizonCStarPerturbationLaw.lean |

## Quantifier and notation audit

- The graph and hypergraph capstones construct canonical real basis coordinates of the **entire** named local Hermitian submodule, with an exact physical-carrier reindexing. They do not merely provide an existential unidentified subfamily.
- Structural graph connectedness, finite types, local dimensions, Hermitian membership, normalized state and positive cutoff describe the objects quantified over. No unproved spectral or Diophantine input remains in either physical capstone.
- The generic event is chosen before matrix observers, weights and cutoff. The finite graph intersection is the reason this is valid; no intersection over uncountably many observers is used.
- Lean uses natural subtraction: capacity minus one and support size minus two are truncated at zero, matching the paper's positive part.
- The formal observer phase uses +itE. Its squared displacement is unchanged by conjugating all phases. The new fidelity transfer verifies the negative-sign Schrödinger amplitude explicitly.
- The nuclear-radius theorem applies to every matrix, hence to density matrices. The conventional factor one half in trace distance is covered by the verified constant-threshold scaling law.
- The stationary theorem lives on the subtype [0,1]; the paper uses the equivalent real interval notation. The top endpoint is proved to lie in support and dominate every support point.
- No density of states, differentiability of the spectral measure, finite moments, or pointwise Fourier decay is assumed by the stationary theorem.
- Bibliographic descriptions report other authors' results; they are not additional unformalized theorems asserted as our own.
