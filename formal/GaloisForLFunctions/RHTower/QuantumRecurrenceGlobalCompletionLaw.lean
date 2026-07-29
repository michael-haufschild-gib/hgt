import GaloisForLFunctions.RHTower.JacobiBoundaryQuantumRecurrenceLaw
import GaloisForLFunctions.RHTower.ObserverRecurrenceDistributionLaw
import GaloisForLFunctions.RHTower.ObserverTemporalUniversalityLaw
import GaloisForLFunctions.RHTower.OptimalLocalFutureEnergyLaw
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Global-completion law for quantum recurrence

This module packages the paper-level result.

* Complete polynomial Krylov geometry and the complete connected Jacobi
  nearest-neighbour rule do not determine the global recurrence phase, even
  for strictly positive energy.
* On a fixed compact positive energy interval, the complete all-orders
  perturbative theory of every bounded continuous spectral observable, and
  the complete all-times spectral-form-factor jet, do not determine the
  exact recurrence phase.
* The missing global datum is measured exactly by the additive collision
  hierarchy of the spectral difference law.  It determines all continuous
  long-time fidelity statistics.

The local causal-horizon law imported above supplies the finite experimental
shadow: every future return probability remains compatible with one finite
nearest-neighbour record, while persistent separation across increasing
depth forces a linear gauge-invariant energy--time cost.  The matching
construction realizes the full future interval with both chain length and
centred energy--time cost linear in the hidden radius.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The two independent exact obstructions that constitute the
global-completion law: an all-depth positive-energy Jacobi obstruction and a
compact-positive-spectrum all-orders perturbative obstruction. -/
structure QuantumRecurrenceGlobalCompletionWitness
    (v : NNReal) (hv : 0 < v) (g : ℝ) (hg : 0 < g) where
  allDepthLocalSeparation :
    PositiveEnergyCompleteLocalJacobiRecurrenceSeparation v hv
  compactRecurrentPlateau :
    recurrencePlateau
        (recurrentCompactSpectrumFamily g : Measure ℝ) =
      Real.exp (-2 / g)
  compactDispersivePlateau :
    recurrencePlateau
        (dispersiveCompactSpectrumFamily g : Measure ℝ) = 0
  completePerturbativeSpectralTheoryEqual :
    perturbativeBoundedSpectralObservableJet
        recurrentCompactSpectrumFamily =
      perturbativeBoundedSpectralObservableJet
        dispersiveCompactSpectrumFamily
  completePerturbativeFormFactorEqual :
    perturbativeSpectralFormFactorJet
        recurrentCompactSpectrumFamily =
      perturbativeSpectralFormFactorJet
        dispersiveCompactSpectrumFamily

/-- **Global-completion law for quantum recurrence.**  For every positive
log-energy variance and every positive coupling, both the exact all-depth
local obstruction and the compact nonperturbative obstruction coexist. -/
theorem quantumRecurrenceGlobalCompletionWitness
    (v : NNReal) (hv : 0 < v) (g : ℝ) (hg : 0 < g) :
    QuantumRecurrenceGlobalCompletionWitness v hv g hg := by
  exact {
    allDepthLocalSeparation :=
      positiveEnergy_completeLocalJacobiRecurrenceSeparation v hv
    compactRecurrentPlateau := by
      simpa [recurrentCompactSpectrumFamily,
        nonperturbativeAtomicCompletion,
        compactPositiveAtomSpectrum] using
        nonperturbativeAtomicCompletion_plateau_instanton_exact
          compactPositiveContinuumSpectrum (3 / 2 : ℝ) hg
    compactDispersivePlateau :=
      dispersiveCompactSpectrumFamily_plateau_zero g
    completePerturbativeSpectralTheoryEqual :=
      perturbativeBoundedSpectralObservableJet_compactFamilies_eq
    completePerturbativeFormFactorEqual :=
      perturbativeSpectralFormFactorJet_compactFamilies_eq
  }

/-- No arbitrary decision rule on complete polynomially local cyclic
Hamiltonian data decides persistent recurrence for all positive-energy
spectra with all moments. -/
theorem globalCompletion_no_completeLocal_recurrenceClassifier
    (v : NNReal) (hv : 0 < v) :
    ¬ ∃ classifier : CompletePolynomialLocalData → Prop,
      ∀ mu : ProbabilityMeasure ℝ,
        HasStrictlyPositiveEnergy (mu : Measure ℝ) →
        HasAllEnergyMoments (mu : Measure ℝ) →
        (classifier
            (completePolynomialLocalData (mu : Measure ℝ)) ↔
          HasPersistentMeanRecurrence (mu : Measure ℝ)) :=
  no_universal_positiveEnergy_completePolynomialLocalData_recurrenceClassifier
    v hv

/-- No arbitrary decision rule on the complete perturbative theory of every
bounded continuous spectral observable decides recurrence throughout the
fixed compact positive-energy class. -/
theorem globalCompletion_no_completePerturbativeTheory_recurrenceClassifier
    (g : ℝ) (hg : 0 < g) :
    ¬ ∃ classifier :
        (BoundedContinuousFunction ℝ ℂ → ℕ → ℂ) → Prop,
      ∀ family : ℝ → ProbabilityMeasure ℝ,
        IsUniformlyCompactPositiveSpectrumFamily family →
        (classifier
            (perturbativeBoundedSpectralObservableJet family) ↔
          HasPersistentMeanRecurrence (family g : Measure ℝ)) :=
  no_universal_compactPositive_completePerturbativeSpectralTheory_recurrenceClassifier
    g hg

/-- No arbitrary decision rule on the complete all-times perturbative
spectral-form-factor jet decides exact recurrence throughout the fixed
compact positive-energy class. -/
theorem globalCompletion_no_completePerturbativeSFF_recurrenceClassifier
    (g : ℝ) (hg : 0 < g) :
    ¬ ∃ classifier : (ℕ → ℝ → ℂ) → Prop,
      ∀ family : ℝ → ProbabilityMeasure ℝ,
        IsUniformlyCompactPositiveSpectrumFamily family →
        (classifier
            (perturbativeSpectralFormFactorJet family) ↔
          HasPersistentMeanRecurrence (family g : Measure ℝ)) :=
  no_universal_compactPositive_completePerturbativeSFF_recurrenceClassifier
    g hg

/-- Global sufficiency law: every continuous statistic of survival fidelity
has a long-time mean for every probability energy spectrum. -/
theorem globalCompletion_everyContinuousReturnStatistic_hasMean
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (statistic : ℝ → ℝ)
    (hstatistic : ContinuousOn statistic (Icc (0 : ℝ) 1)) :
    ∃ L : ℝ,
      Tendsto
        (spectralReturnStatisticMeanReal mu statistic)
        atTop (𝓝 L) :=
  exists_tendsto_spectralReturnStatisticMeanReal
    mu statistic hstatistic

/-- Exact global datum: the `n`-th long-time fidelity moment is the mass at
zero of the `n`-fold additive convolution of the visible gap law. -/
theorem globalCompletion_returnMoments_eq_additiveCollisions
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto (spectralReturnMomentMeanReal mu n) atTop
      (𝓝 ((convPow (spectralDifferenceMeasure mu) n).real {0})) :=
  spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu n

/-- Exact compact-support boundary.  If one representative of a complete
moment sequence is carried by a nondegenerate compact interval, then every
representative is the same measure.  Hence exact all-order local moment data
do determine the global recurrence law in the compact fixed-theory regime. -/
theorem compactExactMoments_determine_spectrum
    {s : ℕ → ℝ} {mu nu : ProbabilityMeasure ℝ}
    {c r : ℝ} (hr : 0 < r)
    (hcarried :
      (mu : Measure ℝ) (Icc (c - r) (c + r))ᶜ = 0)
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (mu : Measure ℝ))
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (nu : Measure ℝ)) :
    (mu : Measure ℝ) = (nu : Measure ℝ) := by
  exact HTGeometry.measure_eq_of_moments_eq_of_one_carried
    hr hcarried
    (fun k => (hmu k).2.symm) (fun k => (hmu k).1)
    (fun k => (hnu k).2.symm) (fun k => (hnu k).1)

/-- In particular, compact exact moment data determine the return plateau. -/
theorem compactExactMoments_determine_recurrencePlateau
    {s : ℕ → ℝ} {mu nu : ProbabilityMeasure ℝ}
    {c r : ℝ} (hr : 0 < r)
    (hcarried :
      (mu : Measure ℝ) (Icc (c - r) (c + r))ᶜ = 0)
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (mu : Measure ℝ))
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (nu : Measure ℝ)) :
    recurrencePlateau (mu : Measure ℝ) =
      recurrencePlateau (nu : Measure ℝ) := by
  rw [compactExactMoments_determine_spectrum hr hcarried hmu hnu]

end RHTower
