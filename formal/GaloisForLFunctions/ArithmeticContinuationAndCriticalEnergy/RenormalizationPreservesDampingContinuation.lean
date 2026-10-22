import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheScalarDampingWorkIsAlreadyPaid
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheResidualCuspForcesEscapingWork
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ContinuationTransportsAdmission

/-!
# Subtracting the constant source preserves the continuation demand

The original energy and its residual at the constant source have uniformly
comparable shifted energies. Their derivatives differ by twice a scalar moment,
already bounded on every positive damping half-line. Thus renormalization neither
solves nor strengthens the missing signed continuation estimate.
-/

open Finset Set RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
noncomputable section
set_option autoImplicit false

private theorem renorm_mass_le (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1))) ≤ 1 := by
  rw [sum_Icc_pronic_mass]
  have h : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
  linarith

/-- Both shifted energies are comparable with one constant for all dampings and horizons. -/
theorem one_add_damped_energy_comparison (η : ℝ) (T : ℕ) :
    1 + pmPowerDampedDualResidual η T ≤ 3 * (1 + dampedMobiusEnergy η T) ∧
      1 + dampedMobiusEnergy η T ≤ 3 * (1 + pmPowerDampedDualResidual η T) := by
  have hD0 : 0 ≤ pmPowerDampedDualResidual η T :=
    Finset.sum_nonneg fun n _ => by positivity
  have hE0 := dampedMobiusEnergy_nonneg η T
  have hDE : pmPowerDampedDualResidual η T ≤ 2 * dampedMobiusEnergy η T + 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 T,
          (2 * pmPowerDampedCenteredDivisorPrefix η n ^ 2 + 2) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n _
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (pmPowerDampedCenteredDivisorPrefix η n + 1)]
      _ = 2 * dampedMobiusEnergy η T +
          2 * ∑ n ∈ Finset.Icc 1 T, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) := by
        unfold dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun n _ => by ring
      _ ≤ _ := by linarith [renorm_mass_le T]
  have hED : dampedMobiusEnergy η T ≤ 2 * pmPowerDampedDualResidual η T + 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 T,
          (2 * (pmPowerDampedCenteredDivisorPrefix η n - 1) ^ 2 + 2) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n _
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (pmPowerDampedCenteredDivisorPrefix η n - 2)]
      _ = 2 * pmPowerDampedDualResidual η T +
          2 * ∑ n ∈ Finset.Icc 1 T, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) := by
        unfold pmPowerDampedDualResidual
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun n _ => by ring
      _ ≤ _ := by linarith [renorm_mass_le T]
  constructor <;> linarith

/-- Admission is unchanged by subtracting the constant source. -/
theorem admits_damped_residual_iff (η : ℝ) :
    Admits pmPowerDampedDualResidual η ↔ Admits dampedMobiusEnergy η := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨3 * (1 + B) - 1, fun T => by
      have := (one_add_damped_energy_comparison η T).2
      linarith [hB T]⟩
  · rintro ⟨B, hB⟩
    exact ⟨3 * (1 + B) - 1, fun T => by
      have := (one_add_damped_energy_comparison η T).1
      linarith [hB T]⟩

/-- The complete work changes by exactly the scalar tangent moment. -/
theorem signedDampingWork_sub_residualDampingWork (η : ℝ) (T : ℕ) :
    signedDampingWork η T - residualDampingWork η T =
      ∑ n ∈ Finset.Icc 1 T, dampedChebyshevError η n /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
  unfold signedDampingWork residualDampingWork
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

private theorem renorm_transport {E F : ℝ → ℕ → ℝ} {E' F' : ℕ → ℝ → ℝ}
    {a c K : ℝ} (hK : 0 ≤ K)
    (hF0 : ∀ η T, 0 ≤ F η T)
    (hEzero : ∀ η, E η 0 = 0) (hE'zero : ∀ η, E' 0 η = 0)
    (hcompare : ∀ η T, 1 + E η T ≤ 3 * (1 + F η T))
    (hpaid : ∀ η ∈ Set.Icc a c, ∀ T, |E' T η - F' T η| ≤ K)
    (h : LinearContinuation E E' a c) : LinearContinuation F F' a c := by
  obtain ⟨β, β', hβ, hwork⟩ := h
  refine ⟨fun η => 3 * β η + K * η, fun η => 3 * β' η + K, ?_, ?_⟩
  · intro η hη
    simpa only [mul_one] using
      ((hβ η hη).const_mul 3).add ((hasDerivAt_id η).const_mul K)
  · intro T η hη
    have hb : 0 ≤ β' η := by
      have hz := hwork 0 η hη
      simpa only [hEzero, hE'zero, neg_zero, add_zero, mul_one] using hz
    have hdiff := (abs_le.mp (hpaid η hη T)).2
    have hbound := mul_le_mul_of_nonneg_left (hcompare η T) hb
    have hKF := mul_nonneg hK (hF0 η T)
    nlinarith [hwork T η hη]

/-- The exact original and residual continuation demands are equivalent on every
positive compact interval. The scalar correction is bounded unconditionally. -/
theorem linearContinuation_residual_iff {a c : ℝ} (ha : 0 < a) :
    LinearContinuation pmPowerDampedDualResidual
        (fun T η => 2 * residualDampingWork η T) a c ↔
      LinearContinuation dampedMobiusEnergy
        (fun T η => 2 * signedDampingWork η T) a c := by
  obtain ⟨K, hK, hpaid⟩ := exists_uniform_scalar_damping_work_bound ha
  have hdiff : ∀ η ∈ Set.Icc a c, ∀ T,
      |2 * signedDampingWork η T - 2 * residualDampingWork η T| ≤ 2 * K := by
    intro η hη T
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      signedDampingWork_sub_residualDampingWork]
    exact mul_le_mul_of_nonneg_left (hpaid η hη.1 T) (by norm_num)
  constructor
  · intro h
    refine renorm_transport (mul_nonneg (by norm_num) hK)
      dampedMobiusEnergy_nonneg
      (fun η => by simp [pmPowerDampedDualResidual])
      (fun η => by simp [residualDampingWork])
      (fun η T => (one_add_damped_energy_comparison η T).1) ?_ h
    intro η hη T
    simpa only [abs_sub_comm] using hdiff η hη T
  · intro h
    refine renorm_transport (mul_nonneg (by norm_num) hK)
      (fun η T => Finset.sum_nonneg fun n _ => by positivity)
      (fun η => by simp [dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy])
      (fun η => by simp [signedDampingWork])
      (fun η T => (one_add_damped_energy_comparison η T).2) hdiff h

end
end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
