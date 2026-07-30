import GaloisForLFunctions.HTGeometry.ObserverActionRecurrenceProjectionLaw
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# All-order recurrence projection of observer action

The quadratic return statistic is only the first replica layer.  At every
replica order, finite survival fidelity is a positive finite polynomial in
projective phase characters.  Consequently one observer-action profile fixes
all return moments simultaneously.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `n`-replica survival-return statistic as a continuous polynomial on
the complete finite phase torus. -/
def finiteReplicaReturnPolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) :
    C(UnitAddTorus I, ℂ) :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      (fidelityReplicaMultiplicityWeight weight p q : ℂ) •
        UnitAddTorus.mFourier
          (replicaMultiplicityCharacter p q)

/-- Replica detuning is exactly the difference of the two total replica
energies. -/
theorem finiteTorusCharacterDetuning_replicaMultiplicityCharacter
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (p q : I → ℕ) :
    finiteTorusCharacterDetuning
        (replicaMultiplicityCharacter p q) energy =
      replicaMultiplicityEnergy energy p -
        replicaMultiplicityEnergy energy q := by
  classical
  unfold finiteTorusCharacterDetuning
    replicaMultiplicityCharacter
    replicaMultiplicityEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change
    ((((p i : ℤ) - (q i : ℤ) : ℤ) : ℝ) * energy i) =
      (p i : ℝ) * energy i - (q i : ℝ) * energy i
  push_cast
  ring

/-- Exact expectation of the replica return polynomial under an arbitrary
phase probability law. -/
theorem integral_finiteReplicaReturnPolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ)
    (μ : ProbabilityMeasure (UnitAddTorus I)) :
    (∫ x, finiteReplicaReturnPolynomial weight n x
        ∂(μ : Measure (UnitAddTorus I))) =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            (∫ x,
              UnitAddTorus.mFourier
                (replicaMultiplicityCharacter p q) x
              ∂(μ : Measure (UnitAddTorus I))) := by
  rw [finiteReplicaReturnPolynomial]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [MeasureTheory.integral_const_mul]
    · intro q hq
      exact
        (by fun_prop :
          Continuous
            (fun x : UnitAddTorus I =>
              (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                UnitAddTorus.mFourier
                  (replicaMultiplicityCharacter p q) x)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro p hp
    exact
      (by fun_prop :
        Continuous
          (fun x : UnitAddTorus I =>
            ∑ q ∈ Finset.univ.piAntidiag n,
              (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                UnitAddTorus.mFourier
                  (replicaMultiplicityCharacter p q) x)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Every finite observation window reports the complete `n`-replica
detuning packet through the same sinc action kernel. -/
theorem integral_finiteReplicaReturnPolynomial_phaseMeasure
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (clock : ℝ) :
    (∫ x, finiteReplicaReturnPolynomial weight n x
        ∂(finiteTorusPhaseProbabilityMeasure energy clock :
          Measure (UnitAddTorus I))) =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            Real.sinc
              (clock *
                (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q)) := by
  rw [integral_finiteReplicaReturnPolynomial]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
    finiteTorusCharacterDetuning_replicaMultiplicityCharacter]

/-- Away from the degenerate zero-radius window, the torus polynomial
expectation is literally the symmetric-time survival-fidelity moment. -/
theorem integral_finiteReplicaReturnPolynomial_phaseMeasure_eq_mean
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) {T : ℝ} (hT : T ≠ 0) :
    (∫ x, finiteReplicaReturnPolynomial weight n x
        ∂(finiteTorusPhaseProbabilityMeasure energy T :
          Measure (UnitAddTorus I))) =
      finiteSpectralSurvivalFidelityMean weight energy n T := by
  rw [integral_finiteReplicaReturnPolynomial_phaseMeasure,
    finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [symmetricPhaseAverage_eq_sinc _ _ hT]

/-- **All-order observer-action recurrence law.** One complete
observer-action profile determines every finite survival-return moment by
evaluation on the replica characters occurring in that moment. -/
theorem integral_finiteReplicaReturnPolynomial_actionProfile
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : ProbabilityMeasure (UnitAddTorus I))
    (profile : (I → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ k : I → ℤ,
      (∫ x, UnitAddTorus.mFourier k x
          ∂(μ : Measure (UnitAddTorus I))) =
        observerActionRegimeCoefficient (profile k))
    (weight : I → ℝ) (n : ℕ) :
    (∫ x, finiteReplicaReturnPolynomial weight n x
        ∂(μ : Measure (UnitAddTorus I))) =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            observerActionRegimeCoefficient
              (profile (replicaMultiplicityCharacter p q)) := by
  rw [integral_finiteReplicaReturnPolynomial]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [hcoeff]

/-- Weak convergence of the complete phase history forces simultaneous
convergence of each prescribed replica return moment to the value selected
by the observer-action profile. -/
theorem finiteReplicaReturn_tendsto_actionProfile
    {α I : Type*} [Fintype I] [DecidableEq I]
    {l : Filter α}
    (energy : α → I → ℝ) (clock : α → ℝ)
    (μ : ProbabilityMeasure (UnitAddTorus I))
    (hμ :
      Tendsto
        (fun x =>
          finiteTorusPhaseProbabilityMeasure
            (energy x) (clock x))
        l (𝓝 μ))
    (profile : (I → ℤ) → ObserverActionRegime)
    (hcoeff : ∀ k : I → ℤ,
      (∫ x, UnitAddTorus.mFourier k x
          ∂(μ : Measure (UnitAddTorus I))) =
        observerActionRegimeCoefficient (profile k))
    (weight : I → ℝ) (n : ℕ) :
    Tendsto
      (fun x =>
        ∫ y, finiteReplicaReturnPolynomial weight n y
          ∂(finiteTorusPhaseProbabilityMeasure
            (energy x) (clock x) :
              Measure (UnitAddTorus I)))
      l
      (𝓝
        (∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
              observerActionRegimeCoefficient
                (profile
                  (replicaMultiplicityCharacter p q)))) := by
  have h :=
    (continuous_integral_complex_continuousMap
      (finiteReplicaReturnPolynomial weight n)).continuousAt.tendsto.comp hμ
  rw [integral_finiteReplicaReturnPolynomial_actionProfile
    μ profile hcoeff weight n] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
