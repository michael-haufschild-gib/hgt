import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalPrescriptionComparison
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalASharpRanges
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalFreeEnergy

/-!
# Actual model-B critical geometry at the same charge and coupling

Transfer the already formalized model-B critical theory to the identical
physical charge/coupling data used in the model-A comparison. Verify the
actual pressure inflection and temperature, the global Gibbs minimum,
and the exact quartic gap. Compare normalized actual fourth derivatives
between prescriptions at their respective critical radii.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

/-- The effective-charge substitution is an identity of whole pressure functions. -/
theorem egbPressureB_effective_charge_function (T Q a : ℝ) :
    egbPressureB T Q a = egbPressureA T (sqrt (Q ^ (2 : ℕ) + a ^ (2 : ℕ))) 0 := by
  funext r
  unfold egbPressureB egbPressureA
  rw [sq_sqrt (by positivity : 0 ≤ Q ^ (2 : ℕ) + a ^ (2 : ℕ))]
  ring

theorem egbPressureB_hasDerivAt (T Q a x : ℝ) :
    HasDerivAt (egbPressureB T Q a)
      (-T / (2 * exp x ^ (2 : ℕ)) + 1 / (4 * Real.pi * exp x ^ (3 : ℕ)) - (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (2 * Real.pi * exp x ^ (5 : ℕ))) (exp x) := by
  rw [egbPressureB_effective_charge_function]
  apply (egbPressureA_hasDerivAt T (sqrt (Q ^ (2 : ℕ) + a ^ (2 : ℕ))) 0 x).congr_deriv
  unfold egbPressureAD1
  rw [sq_sqrt (by positivity : 0 ≤ Q ^ (2 : ℕ) + a ^ (2 : ℕ))]
  ring

theorem egbPressureB_second_derivative (T Q a x : ℝ) :
    deriv (deriv (egbPressureB T Q a)) (exp x) =
      T / exp x ^ (3 : ℕ) - 3 / (4 * Real.pi * exp x ^ (4 : ℕ)) + 5 * (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (2 * Real.pi * exp x ^ (6 : ℕ)) := by
  rw [egbPressureB_effective_charge_function, egbPressureA_second_derivative]
  unfold egbPressureAD2
  rw [sq_sqrt (by positivity : 0 ≤ Q ^ (2 : ℕ) + a ^ (2 : ℕ))]
  ring

/-- Both literal radial pressure derivatives vanish for the same charge/coupling data. -/
theorem egbMatchedCriticalB_pressure_inflection (x θ : ℝ) :
    deriv (egbPressureB (egbMatchedCriticalBTemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ))
      (egbMatchedCriticalBRadius x θ) = 0 ∧
    deriv (deriv (egbPressureB (egbMatchedCriticalBTemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ)))
      (egbMatchedCriticalBRadius x θ) = 0 := by
  have hp := egbMatchedCriticalBRadius_pos x θ
  have he : egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ) = egbMatchedCriticalBRadius x θ ^ (2 : ℕ) / 6 := by
    rw [egbMatchedCriticalBRadius_square]
    ring
  have h₁ := (egbPressureB_hasDerivAt (egbMatchedCriticalBTemperature x θ) (egbCriticalACharge x θ)
    (egbCriticalACouplingRoot x θ) (log (egbMatchedCriticalBRadius x θ))).deriv
  have h₂ := egbPressureB_second_derivative (egbMatchedCriticalBTemperature x θ) (egbCriticalACharge x θ)
    (egbCriticalACouplingRoot x θ) (log (egbMatchedCriticalBRadius x θ))
  simp only [exp_log hp] at h₁ h₂
  constructor
  · rw [h₁, he]
    unfold egbMatchedCriticalBTemperature
    field_simp
    ring
  · rw [h₂, he]
    unfold egbMatchedCriticalBTemperature
    field_simp
    ring

theorem egbMatchedCriticalB_temperature_value (x θ : ℝ) :
    egbTemperatureB (egbMatchedCriticalBPressure x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ)
      (egbMatchedCriticalBRadius x θ) = egbMatchedCriticalBTemperature x θ := by
  have h := egbTemperatureB_pressure (egbMatchedCriticalBTemperature x θ) (egbCriticalACharge x θ)
    (egbCriticalACouplingRoot x θ) (log (egbMatchedCriticalBRadius x θ))
  simp only [exp_log (egbMatchedCriticalBRadius_pos x θ)] at h
  rw [egbMatchedCriticalB_pressure_value] at h
  exact h

def egbMatchedCriticalBLogGibbs (x θ u : ℝ) : ℝ :=
  egbOffShellGibbs (egbMatchedCriticalBPressure x θ) (egbMatchedCriticalBTemperature x θ)
    (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) (exp u)

/-- Exact transfer to the existing canonical model-B critical Gibbs function. -/
theorem egbMatchedCriticalBLogGibbs_canonical (x θ u : ℝ) :
    egbMatchedCriticalBLogGibbs x θ u = egbCriticalLogGibbs (log (egbMatchedCriticalBRadius x θ)) 0 u := by
  have hp := egbMatchedCriticalBRadius_pos x θ
  have he : egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ) = egbMatchedCriticalBRadius x θ ^ (2 : ℕ) / 6 := by
    rw [egbMatchedCriticalBRadius_square]
    ring
  unfold egbMatchedCriticalBLogGibbs egbCriticalLogGibbs egbOffShellGibbs egbMass
  rw [egbCritical_effective_charge, exp_log hp, he]
  unfold egbMatchedCriticalBPressure egbMatchedCriticalBTemperature egbCriticalPressure egbCriticalTemperature
  rw [he, exp_log hp]
  field_simp
  ring

theorem egbMatchedCriticalBLogGibbs_quartic_gap (x θ u : ℝ) :
    egbMatchedCriticalBLogGibbs x θ u - egbMatchedCriticalBRadius x θ / 3 =
      (exp u - egbMatchedCriticalBRadius x θ) ^ (4 : ℕ) / (12 * exp u * egbMatchedCriticalBRadius x θ ^ (2 : ℕ)) := by
  rw [egbMatchedCriticalBLogGibbs_canonical]
  simpa only [exp_log (egbMatchedCriticalBRadius_pos x θ)] using
    egbCriticalLogGibbs_gap (log (egbMatchedCriticalBRadius x θ)) 0 u

theorem egbMatchedCriticalBLogGibbs_global_minimum (x θ u : ℝ) :
    egbMatchedCriticalBRadius x θ / 3 ≤ egbMatchedCriticalBLogGibbs x θ u := by
  rw [egbMatchedCriticalBLogGibbs_canonical]
  simpa only [exp_log (egbMatchedCriticalBRadius_pos x θ)] using
    egbCriticalLogGibbs_lower_bound (log (egbMatchedCriticalBRadius x θ)) 0 u

theorem egbMatchedCriticalBLogGibbs_unique_minimum (x θ u : ℝ) :
    egbMatchedCriticalBLogGibbs x θ u = egbMatchedCriticalBRadius x θ / 3 ↔ u = log (egbMatchedCriticalBRadius x θ) := by
  rw [egbMatchedCriticalBLogGibbs_canonical]
  simpa only [exp_log (egbMatchedCriticalBRadius_pos x θ)] using
    egbCriticalLogGibbs_unique_minimum (log (egbMatchedCriticalBRadius x θ)) 0 u

theorem egbMatchedCriticalBLogGibbs_fourth_derivative (x θ : ℝ) :
    iteratedDeriv 4 (egbMatchedCriticalBLogGibbs x θ) (log (egbMatchedCriticalBRadius x θ)) =
      2 * egbMatchedCriticalBRadius x θ := by
  have he : egbMatchedCriticalBLogGibbs x θ = egbCriticalLogGibbs (log (egbMatchedCriticalBRadius x θ)) 0 :=
    funext (egbMatchedCriticalBLogGibbs_canonical x θ)
  rw [he, egbCriticalLogGibbs_fourth_derivative, exp_log (egbMatchedCriticalBRadius_pos x θ)]

/-- At the same charge and coupling, model A's normalized quartic stiffness is smaller precisely away from zero coupling. -/
theorem egbCritical_prescriptions_stiffness_strict_iff (x θ l : ℝ) :
    iteratedDeriv 4 (egbCriticalALogGibbs x θ l) x / exp x <
      iteratedDeriv 4 (egbMatchedCriticalBLogGibbs x θ) (log (egbMatchedCriticalBRadius x θ)) /
        egbMatchedCriticalBRadius x θ ↔ egbCriticalACouplingRoot x θ ≠ 0 := by
  rw [egbCriticalAStiffness_observable, egbMatchedCriticalBLogGibbs_fourth_derivative]
  have he : 2 * egbMatchedCriticalBRadius x θ / egbMatchedCriticalBRadius x θ = 2 := by
    field_simp [ne_of_gt (egbMatchedCriticalBRadius_pos x θ)]
  rw [he, ← egbCriticalA_shape_pos_iff_coupling_nonzero x θ]
  unfold egbCriticalAStiffness
  have hb := (egbCriticalAShape_bounds θ).1
  rw [div_lt_iff₀ (by positivity : 0 < 1 + 2 * egbCriticalAShape θ)]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.HTGeometry
