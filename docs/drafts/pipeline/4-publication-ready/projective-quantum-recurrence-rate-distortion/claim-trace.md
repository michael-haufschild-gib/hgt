# Internal claim trace — not part of submitted paper

Date: 2026-07-28

Rule: every mathematical statement in `main.tex` and `supplementary.tex` must
be an unconditional theorem in the local proof corpus. Formal verification is
an internal correctness control; it is not a contribution claimed in the
paper.

## Load-bearing claims

| Paper claim | Formal declaration | Source |
|---|---|---|
| Least universal finite Floquet deadline exists | `universalWeightedFloquetFidelityRecurrenceTime_isDeadline` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedFloquetRecurrence.lean` |
| Two-sided water-entropy deadline law with displayed constants | `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich` | same |
| Same theorem in Gaussian rate–distortion notation | `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich` | `formal/GaloisForLFunctions/RHTower/ProjectiveGaussianRateDistortion.lean` |
| Canonical reverse-water-filling allocation is feasible and globally optimal | `projectiveCanonicalWaterEntropy_isGaussianRateDistortionMinimum` | same |
| Pivot minimum is attained | `exists_projectiveGaussianRateDistortion_minimizer` | same |
| Active coordinates contribute exactly the positive logarithms | `projectiveWaterEntropyAt_eq_sum_active` | `formal/GaloisForLFunctions/RHTower/ProjectiveWaterEntropyConsequences.lean` |
| Exact pivot-resolved Haar water budget bounds the one-step target | `measureReal_torusProjectiveWeightedCoherenceTarget_canonicalHaarWater_le` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedHaarQuantileActiveSupport.lean` |
| Fraction of spectra returning through the first `N` clocks | `measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le` | same |
| Complement Haar mass and `1 − α` quantile avoiding return through `N` | `one_sub_canonicalHaarWaterBudget_le_measureReal_avoidance`, `one_sub_alpha_le_measureReal_avoidance_of_canonicalHaarWaterBudget` | same |
| Coarse full-support target budget is an envelope of the exact Haar budget | `projectiveCanonicalHaarWaterBudget_le_projectiveWaterTargetBudget` | same |
| Unsynchronized tail pays twice its weight while selected coordinates pay quadratic defect | `nonnegative_weighted_phaseSum_norm_floor_of_selected_approximation`, `projectiveSelectedWaterDefect_eq_selected_add_discarded` | same |
| Selected-support universal recurrence deadline | `isUniversalProjectiveWeightedCoherenceDeadline_of_selectedFeasible` | same |
| Selected-coordinate logarithmic cost | `log_prod_projectiveSelectedPhaseResolution_le` | same |
| Active-dimension Floquet ceiling | `exists_universalWeightedFloquetFidelityDeadline_of_selectedFeasible` | same |
| Exact weighted projective variance identity | `projectiveWeightedPairwiseEnergy_eq_two_mul_fidelityDeficit` and real covariance results | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedCoherence.lean` |
| Binary hard-support/water-entropy separation at half trace radius | `operationalBinary_supportAndWaterEntropySeparation` | `formal/GaloisForLFunctions/RHTower/ProjectiveOperationalEffectiveSupport.lean` |
| Corresponding binary deadline band | `operationalBinary_floquetTime_waterEntropySandwich` | same |
| Finite observer displacement equals weighted phase energy | `finiteQuantumObserverDistanceSq_eq_phaseEnergy` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverCoherenceLaw.lean` |
| Zero displacement iff phases agree on every graph edge/component | `finiteQuantumObserverPhaseEnergy_eq_zero_iff` | same |
| Exact observer phase capacity `d − components` | `finiteObserverCoherenceGraph_phaseCapacity` | same |
| Joined finite observer capstone | `finite_quantum_observer_coherence_law` | same |
| Graph-rank quantitative recurrence bound | `exists_finiteQuantumObserver_graphRank_distance_recurrence` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverGraphRecurrenceBound.lean` |
| Arbitrary pure-point observer identity | `purePointObserverDistanceSq_eq_phaseEnergy` | `formal/GaloisForLFunctions/RHTower/PurePointQuantumObserverCoherenceLaw.lean` |
| Summability equivalence | `summable_purePointObserver_distance_iff_phaseEnergy` | same |
| Pure-point zero iff every positive nonzero block is phase locked | `purePointObserverPhaseEnergy_eq_zero_iff` | same |
| Hamiltonian pure-point specialization | `purePointHamiltonianObserverDistanceSq_eq_zero_iff` | same |
| Qutrit weights are probabilities and have equal variance | `qutritPeriodicWeight_sum`, `qutritAperiodicWeight_sum`, `qutritPeriodicWeight_nonneg`, `qutritAperiodicWeight_nonneg`, `qutrit_weightedVariance_eq` | `formal/GaloisForLFunctions/RHTower/MixedStateQutritRecurrenceSeparation.lean` |
| Qutrit states are full rank with common spectrum | `qutrit_mixedSpikeState_fullRank`, `qutrit_mixedSpike_spectral_values`, `qutrit_realized_mixedSpike_common_spectral_action` | same |
| Qutrit Hilbert–Schmidt speeds agree and are nonzero | `qutrit_realized_mixedSpikeHSSpeedSq_eq`, `qutrit_common_speed_sq_pos` | same |
| Qutrit SLD quantum Fisher informations agree and are nonzero | `qutrit_realized_mixedSpikeSLDQuantumFisher_eq`, `qutrit_common_quantumFisher_pos` | same |
| Periodic qutrit returns at every tick | `qutritPeriodic_tickRecurrenceAmplitude_eq_zero` | same |
| Aperiodic qutrit inverse-resolution lower bound | `qutritAperiodic_tickRecurrenceAmplitude_lower` | same |
| Aperiodic qutrit matching horizon upper bound | `exists_qutritAperiodic_tickRecurrenceAmplitude_upper` | same |
| Joined qutrit separation | `qutrit_equal_information_global_recurrence_separation` | same |

## Logical assumptions audit

The audit file imported the load-bearing modules and printed axioms for:

- `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich`;
- `measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le`;
- `one_sub_canonicalHaarWaterBudget_le_measureReal_avoidance`;
- `exists_universalWeightedFloquetFidelityDeadline_of_selectedFeasible`;
- `operationalBinary_supportAndWaterEntropySeparation`;
- `finite_quantum_observer_coherence_law`;
- `exists_finiteQuantumObserver_graphRank_distance_recurrence`;
- the pure-point observer zero laws;
- `qutrit_equal_information_global_recurrence_separation`.

All reported only `propext`, `Classical.choice`, and `Quot.sound`. No project
axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration supports a paper
claim.

## Scope checks

- Pure-state upper theorem is discrete Floquet recurrence for every phase
  packet with fixed probabilities. Lower theorem is a normalized-Haar
  population bound over phase packets, not a lower bound for every prescribed
  Hamiltonian. Commensurate spectra can return at the first clock.
- Selected-support theorem charges discarded probability by twice its mass and
  charges rounding cost only on retained coordinates. It does not identify the
  optimizer with the original water active set.
- Observer theorem gives an exact graph capacity and an upper recurrence
  deadline. It does not claim a matching lower bound for every fixed graph.
- Infinite extension gives an exact summable pure-point identity and zero
  law. It does not claim recurrence for continuous spectra.
- Equality with Gaussian rate–distortion is equality of finite convex
  programs, not an operational source-coding equivalence.
- No statement about black holes, inflation, cosmogenesis, the Riemann
  hypothesis, information loss, or an external time variable appears.
