# Internal proof audit

Manuscript: **An arbitrarily weak interaction can reorganize a quantum
system's infinite future**  
Date: 1 August 2026

Rule: every mathematical claim in `main.tex` must be an unconditional theorem
in the local proof corpus. Formal verification is an internal correctness
control and is not presented as scientific novelty in the manuscript.

## Universal coupling law

| Paper claim | Declaration | Source |
|---|---|---|
| Affine character detuning | `projectiveCharacterDetuning_affine` | `CountableRecurrenceWallRayLaw.lean` |
| A transverse character crosses at one explicit strength | `projectiveCharacter_on_affineWall_iff` | same |
| Accidental crossing set is countable | `projectiveAffineCrossingSet_countable` | `AffineCouplingProtectedRelationLaw.lean` |
| Every coupling interval contains a nonexceptional strength | `exists_not_mem_projectiveAffineCrossingSet_in_interval` | same |
| Generic coupled relation iff relation of both inputs | `projectiveCharacter_affineRelation_iff_common_of_not_mem` | same |
| Complete coupled relation set equals exact intersection | `projectiveRelationSet_affine_eq_common_of_not_mem` | same |
| Finite-time coupling reporter is exact sinc profile | `recurrenceWallReporter_eq_sinc` | `CountableRecurrenceWallRayLaw.lean` |
| Exact inverse-time wall profile | `recurrenceWallReporter_scaled_profile` | same |

## Finite conservation and complete interaction conversion

| Paper claim | Declaration | Source |
|---|---|---|
| `τ+ρ=D-1` | `projectiveTemporalRank_add_relationRank` | `UniversalProjectiveRecurrenceCapstoneLaw.lean` |
| `Δτ=-Δρ` on a fixed carrier | `projectiveTemporalRank_sub_eq_relationRank_sub` | `UniversalInteractionRecurrenceConversionLaw.lean` |
| Completed phase law equals relation-lattice indicator | `finiteProjectiveRecurrence_universalLaw` | `UniversalProjectiveRecurrenceCapstoneLaw.lean` |
| Replica character first appears at exact positive height | `spectralCharacterPositiveMass_eq_minimumReplica` and `fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le` | `SpectralCharacterReplicaHeightLaw.lean` and `FidelityReplicaCharacterCoefficientLaw.lean` |
| Generic separable interaction set is dense, residual and full measure | `separableInteractionProjectiveGenericSet_dense_residual_fullMeasure` | `SeparableInteractionProjectiveGenericityLaw.lean` |
| Exceptional set remains null in every parameter region | `separableInteractionProjectiveGenericSet_local_fullMeasure` | same |
| Every generic interaction has full product temporal rank, gain at least `mn`, zero relation rank and all-order collision floor | `mem_separableInteractionProjectiveGenericSet_fullConversion` | same |
| One full-conversion interaction exists inside every positive norm budget, with all-probe Duhamel bound | `exists_smallSeparableInteraction_fullConstraintConversion` | `UniversalInteractionRecurrenceConversionLaw.lean` |
| Deterministic return-frequency Haar sandwich for every generic interaction | `mem_separableInteractionProjectiveGenericSet_recurrenceFrequency` | `GenericInteractionRecurrenceFrequencyLaw.lean` |
| Uniform target has exact half-dimensional volume exponent | `uniformProjectiveCoherenceTarget_volume_bounds` | `UniformProjectiveTargetVolumeExponentLaw.lean` |

## Singular walls and bounded-horizon non-identifiability

| Paper claim | Declaration | Source |
|---|---|---|
| Wall trichotomy, discontinuous completed indicator and exact sinc boundary layer | `recurrenceWall_singularCompletionLaw` | `RecurrenceWallSingularCompletionLaw.lean` |
| Every positive temporal rank is dense | `dense_exactProjectiveTemporalRank` | `ProjectiveRecurrenceDenseStratificationLaw.lean` |
| Temporal-rank map is nowhere continuous | `projectiveTemporalRank_nowhereContinuous` | same |
| Every target rank is indistinguishable by all normalized probes on any bounded horizon | `exists_finiteHorizonIndistinguishable_exactProjectiveTemporalRank` | `FiniteHorizonTemporalDimensionIndistinguishabilityLaw.lean` |
| A different temporal dimension is always bounded-horizon indistinguishable when dimension permits | `exists_finiteHorizonIndistinguishable_differentTemporalDimension` | same |
| Robust recurrence equals base relation intersect perturbation annihilator | `robustProjectiveRelation_iff` | `ProjectiveRecurrenceProtectionLaw.lean` |

## Countable relation hull and separable recurrence ray

| Paper claim | Declaration | Source |
|---|---|---|
| Relation lattice equals compact phase-hull annihilator | `countableRelationHullRecurrenceLaw` | `CountableRelationHullRecurrenceLaw.lean` |
| Every future phase tail has same hull | same | same |
| Every positive summable probe has exact closed recurrent interval, endpoint limits, bounded-window approximation and exact interior hits | same | same |
| Absolute endpoint iff every finite relation has even total coefficient | same | same |
| One arbitrarily weak separable Schatten-1 direction works outside one countable coupling set | `exists_arbitrarilyWeak_separable_completeProjectiveRecurrenceRayLaw` | `SeparableInteractionRecurrenceRayLaw.lean` |
| Same ray preserves maximal domain and self-adjointness | same | same |
| Every nonexceptional strength has every finite temporal rank, full future tails and no nonzero exact global return | same | same |
| Every nonexceptional strength has complete syndetic positive-probe recurrence | same | same |
| Finite-window all-probe bound `2|t||g|δ||O||` | `finiteWindowHeisenberg_affineDirection_norm_sub_le` plus pointwise field returned by ray capstone | `CountableRecurrenceWallRayLaw.lean` and `SeparableInteractionRecurrenceRayLaw.lean` |

## Persistent carrier, finite recovery and earlier clock

| Paper claim | Declaration | Source |
|---|---|---|
| Arbitrary probability spectrum's stationary fidelity law is scaled point-spectrum law | `stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum` | `StationaryRecurrencePointSpectrumScalingLaw.lean` |
| Every stationary fidelity moment is zero-gap collision mass | `spectralReturnMomentMeanReal_tendsto_collisionHierarchy` | `ObserverRecurrenceDistributionLaw.lean` |
| Finite contraction equals semisimple peripheral carrier plus vanishing transient | `finiteContraction_returnAmplitude_eq_persistent_sum_add_transient` | `DissipativeQuantumReturnInformationTransition.lean` |
| Peripheral mass gives exact asymptotic return threshold dichotomy | `finiteContraction_returnThreshold_dichotomy` | same |
| Replica wall coefficient vanishes below height and is positive at height | `resolvedReplicaWallSignal_eq_zero_of_lt_height`, `resolvedReplicaWallCoefficient_pos_at_height` | `ResolvedReplicaRecurrenceWallLaw.lean` |
| `(2n+1)` phase grid exactly recovers every order-`n` coefficient | `finiteGridReplicaCharacterReadout_eq_coefficient_of_bandlimited` | `FiniteGridRecurrenceWallSpectroscopyLaw.lean` |
| Smaller one-coordinate grids fail in worst case | `phaseGridNyquistSharp` | same |
| Phase-cycled coupling scan equals positive coefficient times exact sinc profile at height | `finiteGridControlledWallReadout_eq_resolvedSignal`, `finiteGridControlledWallReadout_scaled_profile`, `resolvedReplicaWallCoefficient_pos_at_height` | same and `ResolvedReplicaRecurrenceWallLaw.lean` |
| Reverse-water recurrence deadline sandwich | `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich` | `ProjectiveWeightedFloquetRecurrence.lean` |
| Same convex program controls Haar target information | `canonicalWaterEntropy_targetInformation_sandwich` | `ProjectiveWeightedTargetVolumeLower.lean` |
| Observer graph projective capacity equals vertices minus components | `finiteObserverCoherenceGraph_phaseCapacity` | `FiniteQuantumObserverCoherenceLaw.lean` |

## Scope audit

- “Universal” refers to the exact relation law for every countable affine
  spectral coupling ray, plus its finite and countable realizations. It does
  not claim coverage of arbitrary continuous-spectrum interacting QFTs.
- “Separable” means operator-Schmidt rank one across spectral factors. It does
  not mean geometric locality or a rank-one operator on product Hilbert space.
- “Temporal dimension” means rational dimension of completed projective phase
  motion, not spacetime dimension.
- Countable exceptional set may be dense; the theorem asserts countability and
  a nonexceptional point in every interval, not an exclusion-free punctured
  neighbourhood.
- No nonzero exact global return coexists with syndetic approximate and exact
  interior-level recurrence; these are different statements.
- Rate--distortion is equality of finite convex programs, not an operational
  communication code.
- Black-hole discussion is a bounded-time inference boundary, not a black-hole
  spectrum, information-loss solution or gravitational prediction.

## Current axiom and syntax audit

Foreground checks passed for:

```text
lake env lean GaloisForLFunctions/HTGeometry/AffineCouplingProtectedRelationLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/SeparableInteractionRecurrenceRayLaw.lean
```

Scratch `#print axioms` for the six new load-bearing declarations reports only:

```text
propext, Classical.choice, Quot.sound
```

Final repository lint and final module build are intentionally pending until
the manuscript freezes.
