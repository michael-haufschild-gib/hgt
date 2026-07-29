# Internal proof audit

Manuscript: **A universal law of quantum recurrence**  
Date: 29 July 2026

Rule: every mathematical claim in `main.tex` must be an unconditional theorem
in the local proof corpus. Formal verification is an internal correctness
control and is not presented as scientific novelty in the manuscript.

## Master capstone

| Paper claim | Declaration | Source |
|---|---|---|
| Complete whether--when--observer--global-data anatomy | `universalQuantumRecurrenceAnatomyLaw` | `formal/GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean` |
| Universal finite-contraction threshold schema | `UniversalFiniteContractionThresholdLaw` | same |
| Coupled contraction/peripheral-packet deadline schema | `UniversalFiniteContractionDeadlineLaw` | same |
| Finite packet rate--distortion clock schema | `UniversalFinitePacketClockLaw` | same |
| Exact finite observer schema | `UniversalFiniteObserverLaw` | same |
| Observer graph deadline schema | `UniversalFiniteObserverClockLaw` | same |
| Arbitrary-spectrum long-time schema | `UniversalLongTimeRecurrenceLaw` | same |
| Pure-point/exact/atomless phase classification | `UniversalSpectralPhaseClassificationLaw` | same |
| Local and perturbative non-identifiability | `UniversalRecurrenceNonidentifiabilityLaw` | same |
| Compact exact-moment determinacy | `UniversalCompactMomentDeterminacyLaw` | same |

## Whether and how much

| Paper claim | Declaration | Source |
|---|---|---|
| Peripheral mass is exact amplitude ceiling | `finiteContraction_returnAmplitude_exactAsymptoticCeiling` | `DissipativeQuantumReturnInformationTransition.lean` |
| Every lower threshold returns after every delay; every higher one is eventually excluded | `finiteContraction_returnThreshold_dichotomy` | same |
| Squared persistent mass is exact fidelity ceiling | `finiteContraction_returnFidelity_exactAsymptoticCeiling` | same |
| Exact persistent/transient spectral decomposition | `finiteContraction_returnAmplitude_eq_persistent_sum_add_transient` | same |
| Transient powers tend to zero | `tendsto_pow_finiteContractionTransientRestriction_zero` | same |
| Finite convex mixtures remain contractive | `norm_finiteMixedEvolution_le_one` | same |

## When

| Paper claim | Declaration | Source |
|---|---|---|
| Least universal Floquet deadline exists | `universalWeightedFloquetFidelityRecurrenceTime_isDeadline` | `ProjectiveWeightedFloquetRecurrence.lean` |
| Return after every prescribed delay by `(M+1)T` | `exists_weightedFloquetFidelity_recurrence_after` | same |
| Reverse-water deadline sandwich | `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich` | same |
| Gaussian rate--distortion form | `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich` | `ProjectiveGaussianRateDistortion.lean` |
| Reverse-water allocation is globally optimal | `projectiveCanonicalWaterEntropy_isGaussianRateDistortionMinimum` | same |
| Coupled finite-contraction water deadline | `finiteContraction_exists_return_at_target_before_waterDeadline` | `DissipativeQuantumReturnInformationTransition.lean` |
| Positive target-volume inner bound | `canonicalEntropyFactor_le_volumeReal_coherenceTarget` | `ProjectiveWeightedTargetVolumeLower.lean` |
| Target-volume upper bound | `volumeReal_coherenceTarget_le_canonicalEntropyFactor` | same |
| Two-sided target-information law | `canonicalWaterEntropy_targetInformation_sandwich` | same |
| Constant-free high-information normalization | `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionNormalized` | `ProjectiveGaussianRateDistortion.lean` |

## What an observer sees

| Paper claim | Declaration | Source |
|---|---|---|
| Observer displacement equals phase energy | `finiteQuantumObserverDistanceSq_eq_phaseEnergy` | `FiniteQuantumObserverCoherenceLaw.lean` |
| Exact return iff every coherence edge locks | `finiteQuantumObserverPhaseEnergy_eq_zero_iff` | same |
| Visible phase dimension equals sectors minus components | `finiteObserverCoherenceGraph_phaseCapacity` | same |
| Joined observer law | `finite_quantum_observer_coherence_law` | same |
| Graph-rank recurrence deadline and displacement bound | `exists_finiteQuantumObserver_graphRank_distance_recurrence` | `FiniteQuantumObserverGraphRecurrenceBound.lean` |
| Deterministic worst-spectrum graph-rank witnesses | `exists_rankSharp_uniformPureObserver_avoiding_return_until` | `FiniteQuantumObserverGraphSharpness.lean` |
| Hilbert--Schmidt normalized probe control | `finiteQuantumObserver_operational_norm_le` | `FiniteQuantumObserverOperationalRecurrence.lean` |
| Operator-normalized probe control with dimension factor | `finiteQuantumObserver_operator_operational_norm_le` | same |
| Dimension factor is attained | `finiteMatrix_operatorContraction_dimension_factor_attained` | same |
| Device coherent-window certificate | `exists_finiteQuantumObserver_graphRank_recurrence_within_window` | `FiniteQuantumObserverDeviceFeasibility.lean` |

## Infinite and arbitrary spectra

| Paper claim | Declaration | Source |
|---|---|---|
| Countable head--tail recurrence bound | `exists_summablePhaseEnergy_recurrence_quantitative` | `SummablePurePointPhaseRecurrence.lean` |
| Every nonnegative summable packet recurs at every resolution | `exists_summablePhaseEnergy_recurrence` | same |
| Exact return iff visible gap group is cyclic | `exists_positive_unitFidelity_iff_cyclic` | `ObserverTemporalUniversalityLaw.lean` |
| Atomless spectra have continuum temporal dimension and zero-density positive-threshold return | `atomlessProjectiveObserverTemporalPhaseLaw` | same |
| `n`th mean fidelity moment equals `n`-fold zero-gap collision mass | `spectralReturnMomentMeanReal_tendsto_collisionHierarchy` | `ObserverRecurrenceDistributionLaw.lean` |
| Every continuous fidelity statistic has a long-time mean | `exists_tendsto_spectralReturnStatisticMeanReal` | same |
| Atomless positive collision moments vanish | `spectralCollisionHierarchy_eq_zero_of_noAtoms` | same |

## Local/global boundary

| Paper claim | Declaration | Source |
|---|---|---|
| Complete polynomial Gram and energy tensors | `completePolynomialLocalData` | `JacobiBoundaryQuantumRecurrenceLaw.lean` |
| Moment-equivalent spectra have identical complete local data | `completePolynomialLocalData_eq_of_hasHamburgerMoments` | same |
| Every indeterminate moment class has pure-point/atomless opposite recurrence completions | `exists_completeLocalJacobiRecurrenceSeparation` | same |
| Strictly-positive-energy explicit separation | `positiveEnergy_completeLocalJacobiRecurrenceSeparation` | same |
| No universal complete-local classifier | `no_universal_positiveEnergy_completePolynomialLocalData_recurrenceClassifier` | same |
| Compact flat families have identical bounded-observable jets | `perturbativeBoundedSpectralObservableJet_compactFamilies_eq` | `NonperturbativeQuantumRecurrenceSeparationLaw.lean` via global capstone |
| Compact flat families have identical full SFF jets | `perturbativeSpectralFormFactorJet_compactFamilies_eq` | same |
| Their exact plateaux are `exp(-2/g)` and `0` | fields of `quantumRecurrenceGlobalCompletionWitness` | `QuantumRecurrenceGlobalCompletionLaw.lean` |
| No all-orders bounded-observable classifier | `globalCompletion_no_completePerturbativeTheory_recurrenceClassifier` | same |
| No all-orders SFF classifier | `globalCompletion_no_completePerturbativeSFF_recurrenceClassifier` | same |
| One compact representative plus all exact moments determines the spectrum | `compactExactMoments_determine_spectrum` | same |

## Scope audit

- “Universal” refers to the joined classification with exact domain at each
  layer. It does not claim one finite deadline for arbitrary continuous
  spectra.
- Rate--distortion means equality of finite convex programs, not an
  operational source code.
- The observer deadline is a worst-spectrum class guarantee, not the first
  return time of every fixed Hamiltonian.
- Atomless zero-density return does not forbid exceptional high-fidelity
  spikes.
- The black-hole result is a certification no-go for perturbative SFF input.
  It does not establish a black-hole spectrum, information recovery or a
  gravitational completion.
- The local onsite-field realization is engineered, not a generic interacting
  ensemble.

## Axiom and syntax audit

Foreground verification:

```text
lake env lean GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean
```

passed. Scratch `#print axioms` for
`universalQuantumRecurrenceAnatomyLaw` reports only:

```text
propext, Classical.choice, Quot.sound
```

Final repository audit:

```text
scripts/formal_tools.py lint
formal lint passed

lake build GaloisForLFunctions.RHTower.UniversalQuantumRecurrenceAnatomyLaw
Build completed successfully (9127 jobs).
```

All build warnings came from pre-existing dependencies; the new capstone
emitted no warning or error.
