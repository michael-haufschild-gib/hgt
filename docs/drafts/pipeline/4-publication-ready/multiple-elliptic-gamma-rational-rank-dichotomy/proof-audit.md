# Proof audit: global-completion law for quantum recurrence

## Scope

Internal dependency-closed claim map for `main.tex`. Manuscript does not
mention formal verification. Novelty or significance receives no credit from
formalization. All mathematical results advertised in title, abstract,
theorems, figure, conclusions, and physical interpretation map to declarations
below.

Capstone audit surface:

- `GaloisForLFunctions.RHTower.QuantumRecurrenceGlobalCompletionLaw`
- theorem `quantumRecurrenceGlobalCompletionWitness`

## Spectral realization and return law

For every probability spectrum:

\[
A_\mu(t)=\int e^{itE}\,d\mu(E),\qquad F_\mu(t)=|A_\mu(t)|^2.
\]

Every probability spectrum has normalized stationary Hilbert clock realization.
Long-time fidelity mean is collision mass of independent energy differences.

Declarations:

- `probabilitySpectrumHilbertClock`
- `every_probability_spectrum_has_cyclicStationaryHilbertClock`
- `inner_realProbCharacterLp_eq_charFun`
- `survivalFormFactor_eq_hilbertClock_overlap_normSq`
- `spectralReturnMeanReal_tendsto_collision`
- `spectralDifferenceMeasure_singleton_zero_iff_noAtoms`
- `recurrencePlateau`
- `HasPersistentMeanRecurrence`

## Theorem 2.1: temporal alternatives

Projective temporal dimension is rational rank of visible energy gaps. For
every probability measure it is at most countable or continuum. Atomless
spectra have continuum dimension, zero mean return, and zero density at every
positive return threshold. Positive exact projective return is equivalent to a
cyclic visible gap group.

Declarations:

- `projectiveObserverTemporalDimension`
- `projectiveObserverTemporalDimension_le_aleph0_or_eq_continuum`
- `exists_positive_projectiveMeasureExactReturn_iff_cyclic`
- `atomlessProjectiveObserverTemporalPhaseLaw`
- `measureTemporalDimension_eq_continuum_of_noAtoms`
- `spectralReturnMeanReal_tendsto_zero_of_noAtoms`
- `highFidelityWindowDensity_tendsto_zero_of_noAtoms`

## Theorem 3.1: all-depth local agreement, opposite recurrence

Complete polynomial local data are

\[
G_\mu(p,q)=\int pq\,d\mu,\qquad
J_\mu(p,q)=\int Epq\,d\mu.
\]

Any two representing measures of one Hamburger moment sequence have identical
`G` and `J`. Every normalized indeterminate class in the bounded-kernel
Nevanlinna regime supplies:

- one countably carried spectrum with positive collision mass and temporal
  dimension at most countable;
- one atomless barycentric spectrum with continuum temporal dimension, zero
  mean return, and zero density at all positive thresholds;
- equality of all local characteristic-function derivatives;
- one common connected Jacobi law at every depth.

Declarations:

- `spectralPolynomialGram`
- `spectralPolynomialEnergyMatrix`
- `spectralPolynomialGram_eq_of_hasHamburgerMoments`
- `spectralPolynomialEnergyMatrix_eq_of_hasHamburgerMoments`
- `CompletePolynomialLocalData`
- `completePolynomialLocalData_eq_of_hasHamburgerMoments`
- `InfiniteJetQuantumRecurrenceSeparation`
- `exists_infiniteJetQuantumRecurrenceSeparation`
- `momentJacobiDiagonal`
- `momentJacobiLower`
- `momentJacobiLower_pos`
- `momentJacobi_threeTerm`
- `CompleteLocalJacobiRecurrenceSeparation`
- `exists_completeLocalJacobiRecurrenceSeparation`

No arbitrary classifier on complete polynomial data decides recurrence
throughout strictly positive spectra with all moments:

- `no_universal_positiveEnergy_completePolynomialLocalData_recurrenceClassifier`
- capstone alias `globalCompletion_no_completeLocal_recurrenceClassifier`

Manuscript caveat is essential: atomless barycenter is not claimed to be an
ordinary self-adjoint extension on same polynomial `ℓ²` closure. Claim is
inequivalent global Hilbert-space completions with identical polynomial local
data.

## Explicit strictly positive pair

For every `v > 0`, discrete positive geometric spectrum and positive lognormal
spectrum have:

- all moments equal to `exp(v n² / 2)`;
- all local derivatives equal;
- strictly positive energy;
- discrete positive collision mass and arbitrarily late full phase recurrence;
- atomless continuous zero mean and zero positive-threshold density;
- identical polynomial Gram and energy-multiplication data;
- identical connected Jacobi rule at every depth.

Declarations:

- `positiveGeometricSpectrum`
- `positiveLognormalSpectrum`
- `integral_pow_positiveGeometricSpectrum`
- `integral_pow_positiveLognormalSpectrum`
- `allLocalDerivativesEqual_positiveSpectra`
- `exists_arbitrarilyLate_positiveGeometricPhaseRecurrence`
- `PositiveEnergyInfiniteJetRecurrenceSeparation`
- `positiveEnergyInfiniteJetRecurrenceSeparation`
- `PositiveEnergyCompleteLocalJacobiRecurrenceSeparation`
- `positiveEnergy_completeLocalJacobiRecurrenceSeparation`

## Compact exact-moment boundary

If one representative of a common moment sequence is carried by a
nondegenerate compact interval, every other representative is carried there
and equals it. Therefore exact compact moment data determine recurrence.

Declarations:

- `measure_compl_Icc_eq_zero_of_moments_eq`
- `measure_eq_of_moments_eq_of_one_carried`
- `compactExactMoments_determine_spectrum`
- `compactExactMoments_determine_recurrencePlateau`

## Theorem 4.1: compact nonperturbative separation

Both families are supported in fixed positive compact interval `[1,2]`.
Recurrent family has one atom of flat mass `exp(-1/g)` for `g > 0`; dispersive
family is uniform atomless measure. Every coupling derivative at zero of every
bounded continuous spectral observable agrees. Complete all-times
spectral-form-factor jets agree. Exact plateaux are `exp(-2/g)` and zero.
Both exact laws have connected Jacobi realizations.

Declarations:

- `compactPositiveContinuumSpectrum`
- `compactPositiveAtomSpectrum`
- `recurrentCompactSpectrumFamily`
- `dispersiveCompactSpectrumFamily`
- `recurrentCompactSpectrumFamily_uniformlyCompactPositive`
- `dispersiveCompactSpectrumFamily_uniformlyCompactPositive`
- `perturbativeBoundedSpectralObservableJet_compactFamilies_eq`
- `perturbativeSpectralFormFactorJet_compactFamilies_eq`
- `nonperturbativeAtomicCompletion_plateau_instanton_exact`
- `recurrentCompactSpectrumFamily_plateau_exact`
- `dispersiveCompactSpectrumFamily_plateau_zero`
- `every_compact_atomlessSpectrum_has_local_perturbativelyInvisible_recurrence`
- `no_universal_compactPositive_completePerturbativeSpectralTheory_recurrenceClassifier`
- `no_universal_compactPositive_completePerturbativeSFF_recurrenceClassifier`
- capstone aliases `globalCompletion_no_completePerturbativeTheory_recurrenceClassifier`
  and `globalCompletion_no_completePerturbativeSFF_recurrenceClassifier`

## Theorem 5.1: complete long-time recurrence law

For every probability spectrum and every natural `n`:

\[
\frac1{2T}\int_{-T}^{T}F_\mu(t)^n\,dt
\longrightarrow ((\Delta\mu)^{*n})(\{0\}).
\]

Every continuous statistic on `[0,1]` has a long-time mean. Polynomial means
are exactly the collision hierarchy; uniform polynomial approximation
determines the continuous-statistic mean. Atomless spectra give evaluation at
zero.

Declarations:

- `charFun_convPow_spectralDifferenceMeasure`
- `spectralReturnMomentMean_eq_integral_sinc`
- `spectralReturnMomentMeanReal_tendsto_collisionHierarchy`
- `spectralCollisionPolynomialMean`
- `spectralReturnStatisticMeanReal_polynomial_tendsto_collisionHierarchy`
- `spectralReturnStatisticMeanReal_dist_le_of_uniform`
- `exists_tendsto_spectralReturnStatisticMeanReal`
- `spectralReturnStatisticMeanReal_tendsto_eval_zero_of_noAtoms`
- capstone aliases `globalCompletion_returnMoments_eq_additiveCollisions`
  and `globalCompletion_everyContinuousReturnStatistic_hasMean`

## Theorem 6.1: complete finite local future set

For every finite radius, positive target time, strict prior window, and
positive tolerance, one finite isospectral self-adjoint connected
nearest-neighbour family:

- agrees exactly on endpoint-local matrix data;
- agrees uniformly within tolerance throughout prior window;
- realizes every target return probability in `[0,1]`.

For fixed target/window/tolerance, one constant `a` works at every radius:

\[
n_R\le 4R+2a+5,\qquad
\Lambda_R\le \pi(4R+2a+5)/(2T).
\]

Thus full ambiguity is achievable with chain length and centred energy-time
cost linear in hidden distance.

Declarations:

- `localHorizon_every_future_probability`
- `localCompatibleFutureSet`
- `exists_localCompatibleFutureSet_eq_Icc`
- `exists_uniformWindowExponent_endpointN_record`
- `FixedEndpointPathModel.norm_le`
- `energyBoundedLocalCompatibleFutureSet`
- `exists_linearEnergy_completeLocalFutureSet`

## Causal bound and matching necessity

For self-adjoint nearest-neighbour Hamiltonians with common radius `R` and
common centred norm bound `Λ`:

\[
|P_A(t)-P_B(t)|
\le 4e^{|t|\Lambda}
\frac{(|t|\Lambda)^{2R+3}}{(2R+3)!}.
\]

At critical action `|t|Λ ≤ (2R+3)/e`, discrepancy is at most
`8 / sqrt(2π(2R+3))`. Persistent cofinal positive discrepancy therefore forces
`|T|Λ_R > (2R+3)/e` eventually. Combined with achievability above, linear
scaling is necessary and sufficient up to universal constants.

Declarations:

- `localCausalHorizon_probability_bound_gauge`
- `localCausalHorizon_probability_bound_critical_gauge`
- `persistentCofinalSeparation_forces_linear_centeredEnergyTime`
- `persistentCofinalSeparation_forces_critical_centeredEnergyTime`

## Thermal spectral-form-factor interpretation

For any normalized thermal spectral probability law, normalized spectral form
factor is `F_mu`; therefore plateau and all long-time continuous statistics are
instances of Theorem 5.1. This is direct substitution into the universal
probability-spectrum theorem, not an additional gravity hypothesis.

Physics conclusion is logical insufficiency only:

- complete local polynomial data do not universally certify recurrence;
- complete perturbative spectral data do not universally certify recurrence;
- exact global spectral completion supplies missing collision data.

## Explicit exclusions

- No claim that an astrophysical black hole realizes constructed spectra.
- No claim that positive plateau equals full information recovery.
- No claim that all model-specific plateaux are nonperturbative.
- No claim that ordinary self-adjoint extensions of one indeterminate Jacobi
  operator include atomless members.
- No claim about gravity equations, black-hole evaporation, entropy value,
  arrow of time, or cosmological initial conditions.
- No novelty or significance claim based on proof formalization.
- No conjecture or open mathematical question appears in manuscript.
