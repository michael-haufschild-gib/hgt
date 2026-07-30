# Proof audit: universal quantum-recurrence information law

Internal audit only. Public manuscript does not mention formal verification.

## Release rule

Every mathematical statement in `main.tex` must be an exact restatement,
specialization, or elementary interpretation of a declaration below. Formal
proof supplies correctness only; it supplies no novelty or significance.

## Master-law claims

| ID | Manuscript claim | Exact declaration | Domain |
|---|---|---|---|
| P1 | Every sampled return moment equals the Fourier pairing of clock law and the corresponding convolution power of the energy-gap law | `clockSampledSpectralReturnMoment_eq_clockTransferCollision` | Every probability measure on real energy, every probability clock on real time, every natural moment order |
| P2 | All sampled moments determine the complete probability law of return, and equality of laws is equivalent to equality of all moments | `clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments` | Arbitrary two system–clock pairs; return lies in `[0,1]` |
| P3 | Clock reflection leaves every return moment unchanged | `clockSampledSpectralReturnMoment_reflected` | Every probability clock, spectrum, and order |
| P4 | Clock symmetrization has characteristic function equal to the real part of the original characteristic function | `charFun_clockOrientationQuotient_eq_re` | Every probability clock |
| P5 | Two balanced energy levels give mean return `(1 + Re φρ(Ω))/2` | `clockSampledSpectralReturnMoment_balancedTwoLevel` | Every probability clock and every real gap |

## Exact maximal quotients

| ID | Manuscript claim | Exact declaration | Domain |
|---|---|---|---|
| Q1 | Two clocks give the same complete return law for every probability spectrum iff their orientation quotients agree | `clockOrientationQuotient_eq_iff_allReturnLaws` | Arbitrary signed real probability clock laws |
| Q2 | Balanced two-level first moments for every gap distinguish exactly the same clock quotient | `clockOrientationQuotient_eq_iff_twoLevelMoments` | Arbitrary signed real probability clock laws |
| Q3 | Two spectra give the same complete return law under every probability clock iff their energy-gap laws agree | `spectralDifferenceMeasure_eq_iff_allClockReturnLaws` | Arbitrary real probability energy laws |
| Q4 | Deterministic first-return moments for every time distinguish exactly the energy-gap quotient | `spectralDifferenceMeasure_eq_iff_deterministicFirstMoments` | Arbitrary real probability energy laws |
| Q5 | Complete universal system equivalence collapses to deterministic first moments | `allClockReturnLaws_eq_iff_deterministicFirstMoments` | Arbitrary real probability energy laws |
| Q6 | Complete universal clock equivalence collapses to balanced two-level first moments | `allReturnLaws_eq_iff_balancedTwoLevelFirstMoments` | Arbitrary signed real probability clock laws |
| Q7 | Rational deterministic times already decide complete universal system equivalence | `allClockReturnLaws_eq_iff_rationalDeterministicFirstMoments` | Arbitrary real probability energy laws |
| Q8 | Rational two-level gaps already decide complete universal clock equivalence | `allReturnLaws_eq_iff_rationalTwoLevelFirstMoments` | Arbitrary signed real probability clock laws |

## Pure-point clock transfer and temporal rank

| ID | Manuscript claim | Exact declaration | Domain |
|---|---|---|---|
| C1 | A finite sampled phase law exists uniquely iff every projective-character clock coefficient converges | `existsUnique_finiteClockSampledPhaseLimit_iff_complete` | Finite real pure-point spectrum, arbitrary probability clocks |
| C2 | Countable analogue with all finite-support characters | `existsUnique_countableClockSampledPhaseLimit_iff_complete` | Countable real pure-point spectrum, arbitrary probability clocks |
| C3 | Temporal dimension plus exact clock-alias rank equals full projective capacity | `finiteClockSampled_temporalDimension_add_aliasRank` | Nonempty finite spectrum |
| C4 | Same two-level spectrum has full revival and temporal dimension zero under deterministic revival sampling, but dimension one under every nonzero continuous uniform window | `unitGapTwoLevelSpectrum_fullRevival_vs_continuous_dimensions` | Explicit unit-gap two-level spectrum |

## Analytic, local, and replica refinements

| ID | Manuscript claim | Exact declaration | Domain |
|---|---|---|---|
| R1 | Every active analytic relation has one exact locked/critical/dephased sinc wall crossing, and the all-horizon atlas reconstructs birth order and critical magnitude | `existsUnique_completeObserverTimeFourierValuationAtlas`; `completeObserverTimeAtlas_uniqueCriticalProfile` | Finite analytic real spectral branches |
| R2 | A balanced character has positive coefficient in the `m`th fidelity moment iff it is realized by two size-`m` multisets; its minimum order is its positive mass | `fidelityReplicaCharacterCoefficient_pos_iff_realizes`; `fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le` | Finite full-support positive weights |
| R3 | Full multinomial expansion used for the exact coefficient formula | `complexFidelityReplicaMultiplicityExpansion` | Finite spectrum |
| R4 | Phase and fidelity visibility occupy the exact northeast cone above the attained valuation/replica corner | `phaseReplicaCharacterVisible_iff_corner_le`; `fidelityMomentCharacterVisible_iff_corner_le` | Active finite analytic character |
| R5 | Hermitian local interactions impose the connected-spanning lower face and attain the explicit local fidelity corner | `exists_localSiteMobiusExplicitFidelityVisibilityCone` | Finite local alphabets and interactions, simple uncoupled product spectrum, active nondegenerate site contrast |
| R6 | Six-level benchmark has the stated first- and second-order birth profiles | `conditionedQubitLayerOne_profile`; `conditionedQubitLayerTwo_profile` and the corresponding conditioned-qubit wall-crossing declarations | Explicit affine Hermitian `6 × 6` family |

## Long-time and infinite-spectrum claims

| ID | Manuscript claim | Exact declaration | Domain |
|---|---|---|---|
| I1 | Symmetric-window moment is the sinc transform of the gap-sum law and converges to its zero atom | `spectralReturnMomentMean_eq_integral_sinc`; `spectralReturnMomentMean_tendsto_collisionHierarchy` | Every probability energy law and every positive order |
| I2 | Every continuous statistic of fidelity has a long-time mean determined by collision moments | `exists_tendsto_spectralReturnStatisticMeanReal` | Every probability energy law |
| I3 | Atomless spectra send every continuous statistic to its value at zero fidelity | `spectralReturnStatisticMeanReal_tendsto_eval_zero_of_noAtoms` | Every atomless probability energy law, including singular-continuous laws |
| I4 | Projective temporal dimension is either at most countable or continuum; no intermediate uncountable value occurs | `projectiveObserverTemporalDimension_le_aleph0_or_eq_continuum` | Every real probability energy law |
| I5 | Arbitrary real observer spectra obey the stated cyclic/aperiodic/atomless phase classification | `universalObserverTemporalPhaseClassification` | Every real probability energy law |
| I6 | Atomless spectra spend asymptotic density zero above every fixed positive fidelity threshold | `highFidelityWindowDensity_tendsto_zero_of_noAtoms` | Every atomless probability energy law |

## Interpretation boundaries

- “Clock orientation” means sign of the real sampling coordinate as seen by
  survival fidelity. It is not a thermodynamic, cosmological, causal, or
  measurement arrow.
- “Temporal dimension” means rational rank/cardinality of the projective
  phase hull visible to the stated probe. It is not extra relativistic
  spacetime dimension.
- “Locality” means the exact connected-packet lower bound in a finite
  Hermitian perturbation family. No Lieb–Robinson velocity or thermodynamic
  limit is claimed.
- Black holes and quantum gravity appear only as motivation. No gravitational
  theorem is claimed.
- The manuscript does not contain the paper-proved but not yet formally
  closed generic nearest-neighbour rank-explosion theorem.

## Current verification status

- `lake env lean GaloisForLFunctions/RHTower/ObserverRecurrenceDistributionLaw.lean`
  passed after adding Q4–Q8.
- Earlier direct module checks passed for the clock, replica, visibility,
  valuation, and temporal-dimension files.
- Final lint, axiom audit, and `lake build <module>` remain release gates.
