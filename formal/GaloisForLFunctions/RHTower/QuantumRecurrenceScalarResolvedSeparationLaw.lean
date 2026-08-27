import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw
import GaloisForLFunctions.RHTower.FiniteAtomicObserverTimeGapLaw
import GaloisForLFunctions.RHTower.ObserverRecurrenceDistributionLaw

/-!
# Scalar recurrence is a strict quotient of resolved recurrence

Survival fidelity is unchanged after reflecting one factor of a product
spectrum.  This gives a general homometric mechanism.  One explicit
nine-level pair has identical scalar survival fidelity at every time and
therefore under every probability clock, but its projective spectral relation
lattices differ.  The complete resolved replica hierarchy distinguishes the
pair.
-/

open MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Product-reflection scalar recurrence law.** Reflecting one factor of a
finite product spectrum leaves survival fidelity unchanged at every time, for
arbitrary real factor weights. -/
theorem finiteSpectralSurvivalFidelity_productReflection
    {I J : Type*} [Fintype I] [Fintype J]
    (weightI energyI : I → ℝ) (weightJ energyJ : J → ℝ)
    (t : ℝ) :
    finiteSpectralSurvivalFidelity
        (fun p : I × J => weightI p.1 * weightJ p.2)
        (fun p : I × J => energyI p.1 + energyJ p.2) t =
      finiteSpectralSurvivalFidelity
        (fun p : I × J => weightI p.1 * weightJ p.2)
        (fun p : I × J => energyI p.1 - energyJ p.2) t := by
  classical
  rw [finiteSpectralSurvivalFidelity_eq_phaseProduct,
    finiteSpectralSurvivalFidelity_eq_phaseProduct]
  simp only [Fintype.sum_prod_type]
  have hplusForward :
      (∑ i, ∑ j,
          (((weightI i * weightJ j : ℝ) : ℂ) *
            Complex.exp
              (((((energyI i + energyJ j) * t : ℝ) : ℂ) *
                Complex.I)))) =
        (∑ i, (weightI i : ℂ) *
            Complex.exp ((((energyI i * t : ℝ) : ℂ) * Complex.I))) *
        (∑ j, (weightJ j : ℂ) *
            Complex.exp ((((energyJ j * t : ℝ) : ℂ) * Complex.I))) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hexp :
        Complex.exp
            (((((energyI i + energyJ j) * t : ℝ) : ℂ) * Complex.I)) =
          Complex.exp ((((energyI i * t : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((energyJ j * t : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  have hplusBackward :
      (∑ i, ∑ j,
          (((weightI i * weightJ j : ℝ) : ℂ) *
            Complex.exp
              ((((-(energyI i + energyJ j) * t : ℝ) : ℂ) *
                Complex.I)))) =
        (∑ i, (weightI i : ℂ) *
            Complex.exp ((((-energyI i * t : ℝ) : ℂ) * Complex.I))) *
        (∑ j, (weightJ j : ℂ) *
            Complex.exp ((((-energyJ j * t : ℝ) : ℂ) * Complex.I))) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hexp :
        Complex.exp
            ((((-(energyI i + energyJ j) * t : ℝ) : ℂ) * Complex.I)) =
          Complex.exp ((((-energyI i * t : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((-energyJ j * t : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  have hminusForward :
      (∑ i, ∑ j,
          (((weightI i * weightJ j : ℝ) : ℂ) *
            Complex.exp
              (((((energyI i - energyJ j) * t : ℝ) : ℂ) *
                Complex.I)))) =
        (∑ i, (weightI i : ℂ) *
            Complex.exp ((((energyI i * t : ℝ) : ℂ) * Complex.I))) *
        (∑ j, (weightJ j : ℂ) *
            Complex.exp ((((-energyJ j * t : ℝ) : ℂ) * Complex.I))) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hexp :
        Complex.exp
            (((((energyI i - energyJ j) * t : ℝ) : ℂ) * Complex.I)) =
          Complex.exp ((((energyI i * t : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((-energyJ j * t : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  have hminusBackward :
      (∑ i, ∑ j,
          (((weightI i * weightJ j : ℝ) : ℂ) *
            Complex.exp
              ((((-(energyI i - energyJ j) * t : ℝ) : ℂ) *
                Complex.I)))) =
        (∑ i, (weightI i : ℂ) *
            Complex.exp ((((-energyI i * t : ℝ) : ℂ) * Complex.I))) *
        (∑ j, (weightJ j : ℂ) *
            Complex.exp ((((energyJ j * t : ℝ) : ℂ) * Complex.I))) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hexp :
        Complex.exp
            ((((-(energyI i - energyJ j) * t : ℝ) : ℂ) * Complex.I)) =
          Complex.exp ((((-energyI i * t : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((energyJ j * t : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  rw [hplusForward, hplusBackward, hminusForward, hminusBackward]
  ring

/-- First factor of the explicit strictness witness. -/
def recurrenceHomometricLeftEnergy : Fin 3 → ℝ := ![0, 1, 4]

/-- Second factor of the explicit strictness witness. -/
def recurrenceHomometricRightEnergy : Fin 3 → ℝ := ![0, 10, 30]

/-- Product-sum spectrum of the explicit strictness witness. -/
def recurrenceHomometricSumEnergy (p : Fin 3 × Fin 3) : ℝ :=
  recurrenceHomometricLeftEnergy p.1 + recurrenceHomometricRightEnergy p.2

/-- Partial-reflection spectrum of the explicit strictness witness. -/
def recurrenceHomometricDifferenceEnergy (p : Fin 3 × Fin 3) : ℝ :=
  recurrenceHomometricLeftEnergy p.1 - recurrenceHomometricRightEnergy p.2

/-- A balanced character that is locked by the sum spectrum but unlocked by
the partial-reflection spectrum. -/
def recurrenceHomometricWitnessCharacter : Fin 3 × Fin 3 → ℤ :=
  Pi.single ((0, 1) : Fin 3 × Fin 3) 1 +
    Pi.single ((1, 0) : Fin 3 × Fin 3) (-10) +
      Pi.single ((0, 0) : Fin 3 × Fin 3) 9

private theorem sum_pi_single
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (z : ℤ) :
    ∑ x, (Pi.single a z : ι → ℤ) x = z := by
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp

private theorem detuning_pi_single
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (z : ℤ) (energy : ι → ℝ) :
    ∑ x, (((Pi.single a z : ι → ℤ) x : ℤ) : ℝ) * energy x =
      (z : ℝ) * energy a := by
  simp [Pi.single_apply, Finset.sum_ite_eq']

theorem recurrenceHomometricWitnessCharacter_balanced :
    SpectralCharacterBalanced recurrenceHomometricWitnessCharacter := by
  unfold SpectralCharacterBalanced recurrenceHomometricWitnessCharacter
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [sum_pi_single, sum_pi_single, sum_pi_single]
  norm_num

theorem recurrenceHomometricWitnessCharacter_sum_detuning :
    finiteTorusCharacterDetuning recurrenceHomometricWitnessCharacter
      recurrenceHomometricSumEnergy = 0 := by
  unfold finiteTorusCharacterDetuning recurrenceHomometricWitnessCharacter
  simp only [Pi.add_apply]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [detuning_pi_single, detuning_pi_single, detuning_pi_single]
  norm_num [recurrenceHomometricSumEnergy,
    recurrenceHomometricLeftEnergy, recurrenceHomometricRightEnergy]

theorem recurrenceHomometricWitnessCharacter_difference_detuning :
    finiteTorusCharacterDetuning recurrenceHomometricWitnessCharacter
      recurrenceHomometricDifferenceEnergy = -20 := by
  unfold finiteTorusCharacterDetuning recurrenceHomometricWitnessCharacter
  simp only [Pi.add_apply]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [detuning_pi_single, detuning_pi_single, detuning_pi_single]
  norm_num [recurrenceHomometricDifferenceEnergy,
    recurrenceHomometricLeftEnergy, recurrenceHomometricRightEnergy]

/-- The explicit homometric spectra have different completed projective
phase geometry. -/
theorem recurrenceHomometric_relationLattices_ne :
    projectiveSpectralRelationLattice recurrenceHomometricSumEnergy ≠
      projectiveSpectralRelationLattice
        recurrenceHomometricDifferenceEnergy := by
  intro h
  have hmem :
      recurrenceHomometricWitnessCharacter ∈
        projectiveSpectralRelationLattice
          recurrenceHomometricSumEnergy := by
    exact ⟨recurrenceHomometricWitnessCharacter_balanced,
      recurrenceHomometricWitnessCharacter_sum_detuning⟩
  have hmem' :
      recurrenceHomometricWitnessCharacter ∈
        projectiveSpectralRelationLattice
          recurrenceHomometricDifferenceEnergy := by
    rw [← h]
    exact hmem
  exact (by
    norm_num [mem_projectiveSpectralRelationLattice_iff,
      recurrenceHomometricWitnessCharacter_difference_detuning] at hmem')

/-- Uniform probability weight on the nine labelled levels. -/
def recurrenceHomometricWeight (_p : Fin 3 × Fin 3) : ℝ := 1 / 9

theorem recurrenceHomometricWeight_nonneg (p : Fin 3 × Fin 3) :
    0 ≤ recurrenceHomometricWeight p := by
  norm_num [recurrenceHomometricWeight]

theorem sum_recurrenceHomometricWeight :
    ∑ p : Fin 3 × Fin 3, recurrenceHomometricWeight p = 1 := by
  rw [Fintype.sum_prod_type]
  norm_num [recurrenceHomometricWeight, Fin.sum_univ_succ]

/-- Probability energy law of the product-sum witness. -/
def recurrenceHomometricSumLaw : ProbabilityMeasure ℝ :=
  ⟨finiteAtomicObserverSpectrum recurrenceHomometricWeight
      recurrenceHomometricSumEnergy,
    finiteAtomicObserverSpectrum_isProbabilityMeasure
      recurrenceHomometricWeight recurrenceHomometricSumEnergy
      recurrenceHomometricWeight_nonneg sum_recurrenceHomometricWeight⟩

/-- Probability energy law of the partial-reflection witness. -/
def recurrenceHomometricDifferenceLaw : ProbabilityMeasure ℝ :=
  ⟨finiteAtomicObserverSpectrum recurrenceHomometricWeight
      recurrenceHomometricDifferenceEnergy,
    finiteAtomicObserverSpectrum_isProbabilityMeasure
      recurrenceHomometricWeight recurrenceHomometricDifferenceEnergy
      recurrenceHomometricWeight_nonneg sum_recurrenceHomometricWeight⟩

/-- The two explicit spectra have identical scalar survival fidelity at every
deterministic time. -/
theorem recurrenceHomometric_normSq_charFun_eq (t : ℝ) :
    Complex.normSq
        (charFun (recurrenceHomometricSumLaw : Measure ℝ) t) =
      Complex.normSq
        (charFun (recurrenceHomometricDifferenceLaw : Measure ℝ) t) := by
  change
    Complex.normSq
        (charFun
          (finiteAtomicObserverSpectrum recurrenceHomometricWeight
            recurrenceHomometricSumEnergy) t) =
      Complex.normSq
        (charFun
          (finiteAtomicObserverSpectrum recurrenceHomometricWeight
            recurrenceHomometricDifferenceEnergy) t)
  rw [charFun_finiteAtomicObserverSpectrum
      recurrenceHomometricWeight recurrenceHomometricSumEnergy
      recurrenceHomometricWeight_nonneg,
    charFun_finiteAtomicObserverSpectrum
      recurrenceHomometricWeight recurrenceHomometricDifferenceEnergy
      recurrenceHomometricWeight_nonneg]
  have h := finiteSpectralSurvivalFidelity_productReflection
    (fun _ : Fin 3 => (1 : ℝ) / 3) recurrenceHomometricLeftEnergy
    (fun _ : Fin 3 => (1 : ℝ) / 3) recurrenceHomometricRightEnergy t
  unfold finiteSpectralSurvivalFidelity finiteSpectralSurvivalAmplitude at h
  norm_num at h
  apply Complex.ofReal_injective
  simpa [recurrenceHomometricWeight, recurrenceHomometricSumEnergy,
    recurrenceHomometricDifferenceEnergy, mul_comm t] using h

/-- The energy-gap laws of the explicit spectra are exactly equal. -/
theorem recurrenceHomometric_spectralDifferenceMeasure_eq :
    spectralDifferenceMeasure
        (recurrenceHomometricSumLaw : Measure ℝ) =
      spectralDifferenceMeasure
        (recurrenceHomometricDifferenceLaw : Measure ℝ) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_spectralDifferenceMeasure,
    charFun_spectralDifferenceMeasure]
  exact_mod_cast recurrenceHomometric_normSq_charFun_eq t

/-- Every scalar survival-return probability law of the explicit pair agrees
under every probability clock. -/
theorem recurrenceHomometric_allClockReturnLaws_eq :
    ∀ clockLaw : ProbabilityMeasure ℝ,
      (clockSampledSpectralReturnProbabilityMeasure
          clockLaw (recurrenceHomometricSumLaw : Measure ℝ) : Measure ℝ) =
        (clockSampledSpectralReturnProbabilityMeasure
          clockLaw
            (recurrenceHomometricDifferenceLaw : Measure ℝ) : Measure ℝ) := by
  exact
    (spectralDifferenceMeasure_eq_iff_allClockReturnLaws
      recurrenceHomometricSumLaw recurrenceHomometricDifferenceLaw).1
        recurrenceHomometric_spectralDifferenceMeasure_eq

/-- Some finite resolved replica detector distinguishes the explicit pair. -/
theorem recurrenceHomometric_exists_resolvedDetector_separation :
    ∃ n k,
      ¬ (ResolvedReplicaDetects recurrenceHomometricSumEnergy n k ↔
        ResolvedReplicaDetects
          recurrenceHomometricDifferenceEnergy n k) := by
  have hnot :
      ¬ ∀ n k,
        (ResolvedReplicaDetects recurrenceHomometricSumEnergy n k ↔
          ResolvedReplicaDetects
            recurrenceHomometricDifferenceEnergy n k) := by
    intro hall
    exact recurrenceHomometric_relationLattices_ne
      ((relationLattice_eq_iff_all_resolvedReplicaDetectors_eq
        recurrenceHomometricSumEnergy
        recurrenceHomometricDifferenceEnergy).2 hall)
  push Not at hnot
  rcases hnot with ⟨n, k, hcase⟩
  refine ⟨n, k, ?_⟩
  tauto

/-- Complete strictness witness: scalar recurrence under every clock is
identical, while completed projective phase geometry and the resolved replica
hierarchy differ. -/
theorem quantumRecurrence_scalarResolved_strictSeparation :
    (∀ clockLaw : ProbabilityMeasure ℝ,
      (clockSampledSpectralReturnProbabilityMeasure
          clockLaw (recurrenceHomometricSumLaw : Measure ℝ) : Measure ℝ) =
        (clockSampledSpectralReturnProbabilityMeasure
          clockLaw
            (recurrenceHomometricDifferenceLaw : Measure ℝ) : Measure ℝ)) ∧
    projectiveSpectralRelationLattice recurrenceHomometricSumEnergy ≠
      projectiveSpectralRelationLattice
        recurrenceHomometricDifferenceEnergy ∧
    ∃ n k,
      ¬ (ResolvedReplicaDetects recurrenceHomometricSumEnergy n k ↔
        ResolvedReplicaDetects
          recurrenceHomometricDifferenceEnergy n k) := by
  exact ⟨recurrenceHomometric_allClockReturnLaws_eq,
    recurrenceHomometric_relationLattices_ne,
    recurrenceHomometric_exists_resolvedDetector_separation⟩

end

end RHTower
