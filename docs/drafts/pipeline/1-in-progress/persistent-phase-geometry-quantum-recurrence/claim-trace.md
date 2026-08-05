# Internal claim trace

Not part of submitted paper. Audit date: 5 August 2026.

## Rule and scope

Every mathematical assertion in `main.tex` and `appendices.tex` must be an
unconditional checked declaration or a direct specialization/composition of
such declarations. Public manuscript contains no formal-verification claims.
All detailed results inherited from three source papers remain in the single
compiled document; Appendix J is completeness ledger.

## Four-law trace

| Unified claim block | Checked declaration or inherited closed trace | Source |
|---|---|---|
| Finite contraction decomposition, persistent ceiling, threshold dichotomy and post-burn-in water deadline | `RHTower.universalQuantumRecurrenceAnatomyLaw`; components `finiteContraction_returnAmplitude_exactAsymptoticCeiling`, `finiteContraction_returnThreshold_dichotomy`, `finiteContraction_exists_return_at_target_before_waterDeadline` | `formal/GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean`; `DissipativeQuantumReturnInformationTransition.lean` |
| Stationary collision hierarchy and means of continuous fidelity statistics | `spectralReturnMomentMeanReal_tendsto_collisionHierarchy`; `exists_tendsto_spectralReturnStatisticMeanReal`; packaged by `RHTower.universalQuantumRecurrenceAnatomyLaw` | `formal/GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean` and imports |
| Countable pure-point recurrence, cyclic exact-return criterion and atomless boundary | `exists_summablePhaseEnergy_recurrence`; `exists_positive_unitFidelity_iff_cyclic`; `atomlessProjectiveObserverTemporalPhaseLaw`; packaged by `RHTower.universalQuantumRecurrenceAnatomyLaw` | same |
| Finite phase hull, balanced relation kernel, temporal rank and `tau + rho = D - 1` | `GaloisForLFunctions.HTGeometry.finiteProjectiveRecurrence_universalLaw` | `formal/GaloisForLFunctions/HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean` |
| Replica height and exact character visibility | fourth conjunct of `finiteProjectiveRecurrence_universalLaw`; detailed phase-grid and sinc declarations in `FidelityReplicaCharacterCoefficientLaw.lean`, `ReplicaPhaseCyclingRecurrenceWallLaw.lean` and `ResolvedReplicaRecurrenceWallLaw.lean` | `formal/GaloisForLFunctions/HTGeometry/` |
| Interaction conservation, protected relations and one-for-one constraint conversion | `phaseLawTemporalDimension_sub_eq_constraintRank_sub`; `projectiveTemporalRank_sub_eq_relationRank_sub`; `exists_smallSeparableInteraction_fullConstraintConversion` | `formal/GaloisForLFunctions/HTGeometry/UniversalInteractionRecurrenceConversionLaw.lean`; inherited audit below |
| Singular walls, sinc profile, dense ranks, bounded-horizon indistinguishability, robust-relation annihilator and countable recurrence ray | Every declaration listed in inherited universal-anatomy proof audit | `../../4-publication-ready/universal-quantum-recurrence-anatomy/proof-audit.md` |
| Static open qudit path: exact path graph, state dimension `q^n`, trace-zero full onsite-plus-edge family, dense/residual/full-measure maximal locus | `exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure` | `formal/GaloisForLFunctions/HTGeometry/NearestNeighborQuditPathGenericityLaw.lean` |
| Static path recurrence consequences: zero balanced kernel, rank `q^n-1`, exact strict-return frequency and no nonzero exact projective return | `exists_uniformQuditPathTracelessRecurrenceGeometry_dense_residual_fullMeasure` | `formal/GaloisForLFunctions/HTGeometry/NearestNeighborQuditPathRecurrenceLaw.lean` |
| Completed-time thermodynamic path law: density extinction, exact Hilbert-dimension rate and double-logarithmic site rate | `thermodynamicProjectiveRecurrenceExtinctionLaw`, with component declarations `quditPathProjectiveReturnDensity_tendsto_zero`, `normalized_neg_log_quditPathProjectiveReturnDensity_tendsto_rate` and `doubleLog_quditPathProjectiveReturnDensity_tendsto_log_q` | `formal/GaloisForLFunctions/HTGeometry/ThermodynamicProjectiveRecurrenceExtinctionLaw.lean` |
| Reverse-water minimizer, product-box/pivot target sandwich, exact information errors, universal deadline, selected support, Haar quantile and onsite-spin transfer | `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich` plus every declaration in inherited projective claim trace | `formal/GaloisForLFunctions/RHTower/ProjectiveGaussianRateDistortion.lean`; `../../4-publication-ready/projective-quantum-recurrence-rate-distortion/claim-trace.md` |
| Finite observer phase energy, graph zero set and exact capacity | `finite_quantum_observer_coherence_law` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverCoherenceLaw.lean` |
| Sharp graph exponent, probes, calibration/device-window bounds, countable observer extension and equal-qutrit local/global separation | Every declaration in inherited projective claim trace; observer components packaged by `RHTower.universalQuantumRecurrenceAnatomyLaw` | inherited projective trace above |
| Positive binomial/parity measures, one Hamiltonian, uniform field, fixed protocol/spectrum, nearest-neighbour form, forced endpoint disconnection, occupation and all-sector lifts, moments/window/every future | `RHTower.ParityForecast.one_fixed_nearestNeighbor_freeFermion_every_future_probability` plus every declaration in inherited local-clock trace | `formal/GaloisForLFunctions/RHTower/FermionicFockIsospectrality.lean`; `../../4-publication-ready/local-quantum-clock-recurrence/claim-trace.md` |
| Sharp support threshold and minimax forecast error `1/2` | `RHTower.ParityForecast.every_forecaster_has_half_error` and local-clock sharpness declarations | `formal/GaloisForLFunctions/RHTower/ParityConditionedForecastingInstability.lean`; inherited local-clock trace |
| Global local/perturbative nonidentifiability and compact moment determinacy | `RHTower.universalQuantumRecurrenceAnatomyLaw`, fields `localDataDoNotDecide` and `compactExactDataDecide` | `formal/GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean` |

## New path theorem specialist trace

1. `connected_subgraph_comap_path_eq` proves architecture graph is whole open
   path, not a subgraph hidden inside a denser interaction graph.
2. `exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`
   works in exact trace-zero local submodule and reports density, residuality
   and null complement in intrinsic coefficient coordinates.
3. `MaximallyProjectiveEnergy` removes every nonconstant balanced rational,
   hence integer, relation and implies simple spectrum.
4. `anchoredTemporalRank_eq_card_sub_one_of_maximallyProjective` gives
   `q^n - 1` after physical/spectral cardinalities are identified.
5. `maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency` gives exact
   Haar frequency for strict coordinatewise target.
6. `MaximallyProjectiveEnergy.no_nonzeroExactAnchoredReturn` excludes every
   nonzero real return time; `n,q >= 2` supplies at least four levels.
7. `thermodynamicProjectiveRecurrenceExtinctionLaw` packages positivity,
   extinction and both exact rates from
   `quditPathProjectiveReturnDensity_tendsto_zero`,
   `normalized_neg_log_quditPathProjectiveReturnDensity_tendsto_rate` and
   `doubleLog_quditPathProjectiveReturnDensity_tendsto_log_q` prove the
   sequential completed-time-then-size density law and its two exact rates.

## Axiom audit

Scratch `lake env lean` audits check all inherited load-bearing capstones and
the three thermodynamic declarations. Every `#print axioms` report is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No project `axiom`, `sorry`, `admit`, `opaque` or `unsafe` declaration enters
the proof surface. `scripts/formal_tools.py lint --check-generated` passes.

## Scope exclusions

No manuscript theorem claims translation-invariant genericity, a sharp first
return exponent for each fixed Hamiltonian, recurrence of a global
infinite-volume orbit, interchange of time and size limits, circuit
complexity growth, or identifiability from full tomography.  The only
thermodynamic statement is the proved sequential limit of finite-volume
completed-time return densities.
