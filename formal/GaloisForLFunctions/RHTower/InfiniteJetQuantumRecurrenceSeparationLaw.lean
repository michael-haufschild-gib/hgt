import GaloisForLFunctions.HTGeometry.NevBauerUnconditional
import GaloisForLFunctions.HTGeometry.NevFiberCountable
import GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual
import GaloisForLFunctions.RHTower.ObserverTemporalDimensionLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Infinite-jet quantum recurrence separation

Every normalized indeterminate Hamburger moment class contains two probability
spectra whose characteristic functions have the same complete Taylor jet at
time zero but occupy incompatible global temporal phases.  A countably carried
Nevanlinna leaf has positive asymptotic mean return fidelity and at-most-
countable temporal dimension.  An atomless Nevanlinna barycenter has vanishing
asymptotic mean return fidelity, zero density at every positive return
threshold, and continuum temporal dimension.
-/

open Filter MeasureTheory Set
open scoped Cardinal OnePoint Topology

noncomputable section

namespace RHTower

/-- Complete moments give every finite `L^n` energy norm required to
differentiate the characteristic function `n` times. -/
theorem hasHamburgerMoments_memLp_id
    {s : ℕ → ℝ} {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (n : ℕ) :
    MemLp id n mu := by
  by_cases hn : n = 0
  · subst n
    simpa using
      (memLp_zero_iff_aestronglyMeasurable.mpr
        (show AEStronglyMeasurable (id : ℝ → ℝ) mu by fun_prop))
  · apply (integrable_norm_rpow_iff (f := id) (by fun_prop)
      (by exact_mod_cast hn) (by simp)).mp
    have hnorm := (hmu n).1.norm
    simpa [Real.norm_eq_abs, abs_pow] using hnorm

/-- Measures with the same complete Hamburger moments have identical
characteristic-function derivatives of every order at time zero. -/
theorem iteratedDeriv_charFun_zero_eq_of_hasHamburgerMoments
    {s : ℕ → ℝ} {mu nu : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s mu)
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu)
    (n : ℕ) :
    iteratedDeriv n (charFun mu) 0 =
      iteratedDeriv n (charFun nu) 0 := by
  rw [iteratedDeriv_charFun_zero
      (hasHamburgerMoments_memLp_id hmu n),
    iteratedDeriv_charFun_zero
      (hasHamburgerMoments_memLp_id hnu n),
    (hmu n).2, (hnu n).2]

/-- A probability measure carried by a countable set cannot be atomless. -/
theorem not_noAtoms_of_probability_carried_countable
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {carrier : Set ℝ} (hcarrier : carrier.Countable)
    (hcarried : mu carrierᶜ = 0) :
    ¬NullSingletonClass mu := by
  intro hnoAtoms
  letI : NullSingletonClass mu := hnoAtoms
  have hzero : mu carrier = 0 :=
    hcarrier.measure_zero mu
  have hone : mu carrier = 1 := by
    rw [measure_of_measure_compl_eq_zero hcarried, measure_univ]
  exact zero_ne_one (hzero.symm.trans hone)

/-- Countable support forces at-most-countable observer temporal dimension. -/
theorem measureTemporalDimension_le_aleph0_of_support_countable
    (mu : Measure ℝ) (hsupport : mu.support.Countable) :
    SpectralMemory.measureTemporalDimension mu ≤ Cardinal.aleph0 := by
  rw [SpectralMemory.measureTemporalDimension,
    SpectralMemory.measureVisibleFrequencyModule]
  exact (rank_span_le mu.support).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr hsupport)

/-- The complete all-order local-time data and the incompatible global
recurrence phases extracted from one moment class. -/
structure InfiniteJetQuantumRecurrenceSeparation (s : ℕ → ℝ) where
  recurrentSpectrum : ProbabilityMeasure ℝ
  dispersiveSpectrum : ProbabilityMeasure ℝ
  recurrentMoments :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (recurrentSpectrum : Measure ℝ)
  dispersiveMoments :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      (dispersiveSpectrum : Measure ℝ)
  allLocalDerivativesEqual :
    ∀ n : ℕ,
      iteratedDeriv n (charFun (recurrentSpectrum : Measure ℝ)) 0 =
        iteratedDeriv n (charFun (dispersiveSpectrum : Measure ℝ)) 0
  recurrentTemporalDimension :
    SpectralMemory.measureTemporalDimension
      (recurrentSpectrum : Measure ℝ) ≤ Cardinal.aleph0
  dispersiveTemporalDimension :
    SpectralMemory.measureTemporalDimension
      (dispersiveSpectrum : Measure ℝ) = Cardinal.continuum
  recurrentCollisionMassPositive :
    0 <
      (spectralDifferenceMeasure
        (recurrentSpectrum : Measure ℝ)).real {0}
  recurrentMeanReturn :
    Tendsto
      (spectralReturnMeanReal (recurrentSpectrum : Measure ℝ))
      atTop
      (𝓝
        ((spectralDifferenceMeasure
          (recurrentSpectrum : Measure ℝ)).real {0}))
  dispersiveMeanReturn :
    Tendsto
      (spectralReturnMeanReal (dispersiveSpectrum : Measure ℝ))
      atTop (𝓝 0)
  dispersivePositiveThresholdDensity :
    ∀ eta : ℝ, 0 < eta →
      Tendsto
        (highFidelityWindowDensity
          (dispersiveSpectrum : Measure ℝ) eta)
        atTop (𝓝 0)

/-- **Infinite-jet quantum recurrence separation law.** For every normalized
positive definite Hamburger moment sequence with bounded kernel, hence for
every indeterminate normalized Hamburger moment class, complete local
survival data coexist with incompatible global temporal phases. -/
theorem exists_infiniteJetQuantumRecurrenceSeparation
    {s : ℕ → ℝ} (h : HTGeometry.PositiveMomentForm s)
    (h0b : HTGeometry.BoundedKernel s 0) (h0 : s 0 = 1) :
    Nonempty (InfiniteJetQuantumRecurrenceSeparation s) := by
  let recurrent : ProbabilityMeasure ℝ :=
    HTGeometry.nevLeaf h h0b h0 (↑(0 : ℝ) : OnePoint ℝ)
  let boundary := HTGeometry.nevBoundaryFamily h h0b h0
  obtain ⟨eta, heta⟩ :=
    GaloisForLFunctions.HTGeometry.projectiveSingularContinuousProbabilityLaws_dense.nonempty
  have hetaNoAtoms :
      NullSingletonClass (eta : Measure (OnePoint ℝ)) :=
    heta.1
  let dispersive : ProbabilityMeasure ℝ :=
    boundary.barycenter eta
  have hrecurrentMoments :
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
        (recurrent : Measure ℝ) :=
    HTGeometry.nevLeaf_hasHamburgerMoments h h0b h0
      (↑(0 : ℝ) : OnePoint ℝ)
  have hdispersiveMoments :
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
        (dispersive : Measure ℝ) :=
    boundary.barycenter_hasHamburgerMoments eta
  have hdispersiveNoAtoms :
      NullSingletonClass (dispersive : Measure ℝ) := by
    letI : NullSingletonClass (eta : Measure (OnePoint ℝ)) :=
      hetaNoAtoms
    exact boundary.barycenter_noAtoms eta
  let recurrentCarrier : Set ℝ :=
    (HTGeometry.nevMatrixDataInf h h0b).finiteDenominatorFiber 0
  have hrecurrentCarrierCountable :
      recurrentCarrier.Countable :=
    HTGeometry.countable_finiteDenominatorFiber h h0b 0
  have hrecurrentCarried :
      (recurrent : Measure ℝ) recurrentCarrierᶜ = 0 :=
    HTGeometry.nevLeaf_finite_carried h h0b h0 0
  have hrecurrentNotNoAtoms :
      ¬NullSingletonClass (recurrent : Measure ℝ) :=
    not_noAtoms_of_probability_carried_countable
      (recurrent : Measure ℝ)
      hrecurrentCarrierCountable hrecurrentCarried
  have hrecurrentSupport :
      (recurrent : Measure ℝ).support ⊆ recurrentCarrier := by
    apply Measure.support_subset_of_isClosed
      (HTGeometry.isClosed_finiteDenominatorFiber h h0b 0)
    rw [mem_ae_iff]
    exact hrecurrentCarried
  have hrecurrentSupportCountable :
      (recurrent : Measure ℝ).support.Countable :=
    hrecurrentCarrierCountable.mono hrecurrentSupport
  have hrecurrentCollisionNe :
      spectralDifferenceMeasure (recurrent : Measure ℝ) {0} ≠ 0 := by
    intro hzero
    exact hrecurrentNotNoAtoms
      ((spectralDifferenceMeasure_singleton_zero_iff_noAtoms
        (recurrent : Measure ℝ)).mp hzero)
  have hrecurrentCollisionPositive :
      0 <
        (spectralDifferenceMeasure
          (recurrent : Measure ℝ)).real {0} := by
    rw [Measure.real]
    exact ENNReal.toReal_pos hrecurrentCollisionNe
      (measure_ne_top _ _)
  letI : NullSingletonClass (dispersive : Measure ℝ) :=
    hdispersiveNoAtoms
  refine ⟨{
    recurrentSpectrum := recurrent
    dispersiveSpectrum := dispersive
    recurrentMoments := hrecurrentMoments
    dispersiveMoments := hdispersiveMoments
    allLocalDerivativesEqual := fun n =>
      iteratedDeriv_charFun_zero_eq_of_hasHamburgerMoments
        hrecurrentMoments hdispersiveMoments n
    recurrentTemporalDimension :=
      measureTemporalDimension_le_aleph0_of_support_countable
        (recurrent : Measure ℝ) hrecurrentSupportCountable
    dispersiveTemporalDimension :=
      SpectralMemory.measureTemporalDimension_eq_continuum_of_noAtoms
        (dispersive : Measure ℝ)
    recurrentCollisionMassPositive :=
      hrecurrentCollisionPositive
    recurrentMeanReturn :=
      spectralReturnMeanReal_tendsto_collision
        (recurrent : Measure ℝ)
    dispersiveMeanReturn :=
      spectralReturnMeanReal_tendsto_zero_of_noAtoms
        (dispersive : Measure ℝ)
    dispersivePositiveThresholdDensity := fun eta heta =>
      highFidelityWindowDensity_tendsto_zero_of_noAtoms
        (dispersive : Measure ℝ) heta
  }⟩

end RHTower
