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
| A return occurs after every prescribed delay `M`, by `(M+1)T` | `exists_weightedFloquetFidelity_recurrence_after` | same |
| Two-sided water-entropy deadline law with displayed constants | `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich` | same |
| Same theorem in Gaussian rate–distortion notation | `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich` | `formal/GaloisForLFunctions/RHTower/ProjectiveGaussianRateDistortion.lean` |
| Canonical reverse-water-filling allocation is feasible and globally optimal | `projectiveCanonicalWaterEntropy_isGaussianRateDistortionMinimum` | same |
| Pivot minimum is attained | `exists_projectiveGaussianRateDistortion_minimizer` | same |
| Active coordinates contribute exactly the positive logarithms | `projectiveWaterEntropyAt_eq_sum_active` | `formal/GaloisForLFunctions/RHTower/ProjectiveWaterEntropyConsequences.lean` |
| Exact pivot-resolved Haar water budget bounds the one-step target | `measureReal_torusProjectiveWeightedCoherenceTarget_canonicalHaarWater_le` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedHaarQuantileActiveSupport.lean` |
| Explicit feasible product box lies inside the true coherence target | `projectiveWaterProduct_le_volumeReal_coherenceTarget` | `formal/GaloisForLFunctions/RHTower/ProjectiveWeightedTargetVolumeLower.lean` |
| Exact box product equals dimension factor times water entropy | `projectiveWaterProduct_eq_entropy` | same |
| Canonical positive lower target-volume law | `canonicalEntropyFactor_le_volumeReal_coherenceTarget` | same |
| Canonical upper target-volume law with the same entropy minimum | `volumeReal_coherenceTarget_le_canonicalEntropyFactor` | same |
| True target volume is strictly positive | `volumeReal_coherenceTarget_pos` | same |
| Two-sided target-information law | `canonicalWaterEntropy_targetInformation_sandwich` | same |
| Absolute and relative target-information remainder bounds | `abs_targetInformation_sub_canonicalWaterEntropy_le`, `abs_targetInformation_div_canonicalWaterEntropy_sub_one_le` | same |
| Every torus phase packet is realized by independent onsite energies in the single-excitation block of a Hermitian local spin Hamiltonian | `exp_I_torusIndependentOnsiteFieldEnergy`, `independentOnsiteField_localSpin_singleExcitation_block` | `formal/GaloisForLFunctions/RHTower/LocalSpinPhaseEnsembleTransfer.lean` |
| Exact local onsite-field target equals the projective target, with identical Haar volume | `torusIndependentOnsiteFieldReturnTarget_eq_projective`, `measureReal_torusIndependentOnsiteFieldReturnTarget_eq_projective` | same |
| Both water-volume bounds transfer exactly to the local onsite-field ensemble | `canonicalEntropyFactor_le_volumeReal_independentOnsiteFieldReturnTarget`, `volumeReal_independentOnsiteFieldReturnTarget_le_canonicalEntropyFactor` | same |
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
| Every normalized linear probe is controlled by total observer distance | `finiteQuantumObserver_operational_sq_le`, `finiteQuantumObserver_operational_norm_le` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverOperationalRecurrence.lean` |
| Self-adjoint Hilbert–Schmidt pairing equals trace expectation | `finiteMatrixHSFunctional_eq_trace_mul_of_selfAdjoint` | same |
| Two-calibration-error operational bound | `finiteQuantumObserver_operational_noise_le` | same |
| Every operator contraction has Hilbert–Schmidt energy at most the matrix dimension | `finiteMatrixHSEnergy_le_dimension_of_operatorContraction` | same |
| Operator-normalized probe transfer with explicit dimension factor | `finiteQuantumObserver_operator_operational_sq_le`, `finiteQuantumObserver_operator_operational_norm_le` | same |
| The general operator-to-Hilbert–Schmidt dimension factor is attained | `finiteMatrix_operatorContraction_dimension_factor_attained` | same |
| Operator-normalized two-calibration-error bound | `finiteQuantumObserver_operator_operational_noise_le_sqrt_dimension` | same |
| Graph recurrence occurs inside a coherent device window whenever the certified horizon fits | `exists_finiteQuantumObserver_graphRank_recurrence_within_window` | `formal/GaloisForLFunctions/RHTower/FiniteQuantumObserverDeviceFeasibility.lean` |
| Arbitrary pure-point observer identity | `purePointObserverDistanceSq_eq_phaseEnergy` | `formal/GaloisForLFunctions/RHTower/PurePointQuantumObserverCoherenceLaw.lean` |
| Summability equivalence | `summable_purePointObserver_distance_iff_phaseEnergy` | same |
| Pure-point zero iff every positive nonzero block is phase locked | `purePointObserverPhaseEnergy_eq_zero_iff` | same |
| Hamiltonian pure-point specialization | `purePointHamiltonianObserverDistanceSq_eq_zero_iff` | same |
| Quantitative countable finite-head/summable-tail recurrence | `exists_summablePhaseEnergy_recurrence_quantitative` | `formal/GaloisForLFunctions/RHTower/SummablePurePointPhaseRecurrence.lean` |
| Every nonnegative summable countable phase packet recurs below every positive energy resolution | `exists_summablePhaseEnergy_recurrence` | same |
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
- `exists_weightedFloquetFidelity_recurrence_after`;
- `canonicalWaterEntropy_targetInformation_sandwich`;
- `abs_targetInformation_div_canonicalWaterEntropy_sub_one_le`;
- `measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le`;
- `one_sub_canonicalHaarWaterBudget_le_measureReal_avoidance`;
- `exists_universalWeightedFloquetFidelityDeadline_of_selectedFeasible`;
- `operationalBinary_supportAndWaterEntropySeparation`;
- `finite_quantum_observer_coherence_law`;
- `exists_finiteQuantumObserver_graphRank_distance_recurrence`;
- `finiteQuantumObserver_operational_noise_le`;
- the local-spin phase-target equality and two transferred volume bounds;
- the operator-contraction energy, sharpness, response and calibration laws;
- `exists_finiteQuantumObserver_graphRank_recurrence_within_window`;
- `exists_summablePhaseEnergy_recurrence_quantitative`;
- `exists_summablePhaseEnergy_recurrence`;
- the pure-point observer zero laws;
- `qutrit_equal_information_global_recurrence_separation`.

All reported only `propext`, `Classical.choice`, and `Quot.sound`. No project
axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration supports a paper
claim. Final audit on 28 July 2026 passed
`scripts/formal_tools.py lint`,
`lake build GaloisForLFunctions.RHTower.QuantumRecurrenceUniversality`, and a
foreground `lake env lean` axiom report covering every load-bearing theorem.

## Scope checks

- Pure-state target information is two-sided for normalized Haar geometry.
  The finite-horizon hit law remains one-sided because power-map targets are
  correlated. The universal deadline is minimax over all compatible phase
  packets, not a lower bound for every prescribed Hamiltonian. Commensurate
  spectra can return at the first clock.
- Selected-support theorem charges discarded probability by twice its mass and
  charges rounding cost only on retained coordinates. It does not identify the
  optimizer with the original water active set.
- Observer theorem gives an exact graph capacity and an upper recurrence
  deadline. It does not claim a matching lower bound for every fixed graph.
- Infinite extension gives both genuine recurrence for every nonnegative
  summable countable phase energy and an exact summable pure-point observer
  identity and zero law. It does not claim recurrence for continuous spectra.
- Equality with Gaussian rate–distortion is equality of finite convex
  programs, not an operational source-coding equivalence.
- Haar phase geometry now has an exact realization by an engineered
  independently tunable onsite-field local spin ensemble. This does not say
  that generic interacting local-Hamiltonian spectra are Haar.
- Operator-normalized probes pay an explicit square-root dimension
  conversion. The dimension-free matrix-pairing claim is not made.
- Device feasibility is certified when the theorem's horizon times the
  measured tick duration fits inside the measured coherent window. The paper
  does not claim that every current device satisfies this inequality.
- No statement about black holes, inflation, cosmogenesis, the Riemann
  hypothesis, information loss, or an external time variable appears.
