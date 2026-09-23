import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalParameters
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAQuarticAsymptotic
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAEOS

/-!
# The fixed-charge endpoint is the actual model-A critical state

Transport the equation-of-state inflection, unique global Gibbs minimum,
and positive physical-radius quartic limit to the same fixed electric
charge and Gauss–Bonnet coupling as the coexistence path.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeACritical_temperature_function (w φ : ℝ) :
    egbTemperatureA (egbCriticalAPressure (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ))
      (egbCriticalACharge (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) (egbCriticalACouplingRoot (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) =
        egbTemperatureA (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ) := by
  funext r
  rw [egbFixedChargeACritical_pressure_transfer]
  unfold egbTemperatureA
  rw [egbFixedChargeACritical_charge_square, egbFixedChargeACritical_coupling_square]

theorem egbFixedChargeACritical_pressure_function (w φ : ℝ) :
    egbPressureA (egbCriticalATemperature (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ))
      (egbCriticalACharge (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) (egbCriticalACouplingRoot (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) =
        egbPressureA (egbFixedChargeACriticalTemperature w φ) (exp w * cos φ) (exp w * sin φ) := by
  funext r
  rw [egbFixedChargeACritical_temperature_transfer]
  unfold egbPressureA
  rw [egbFixedChargeACritical_charge_square, egbFixedChargeACritical_coupling_square]

theorem egbFixedChargeACritical_gibbs_function (w φ l : ℝ) :
    egbOffShellGibbsA (egbCriticalAPressure (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) (egbCriticalATemperature (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ))
      (egbCriticalACharge (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) (egbCriticalACouplingRoot (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)) l =
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l := by
  funext r
  rw [egbFixedChargeACritical_pressure_transfer, egbFixedChargeACritical_temperature_transfer]
  unfold egbOffShellGibbsA egbMass egbEntropyA
  rw [egbFixedChargeACritical_charge_square, egbFixedChargeACritical_coupling_square]

theorem egbFixedChargeACritical_temperature_value (w φ : ℝ) :
    egbTemperatureA (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeACriticalRadius w φ) = egbFixedChargeACriticalTemperature w φ := by
  have h := egbCriticalA_temperature_value (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACritical_temperature_function, egbFixedChargeACriticalLogScale_exp,
    egbFixedChargeACritical_temperature_transfer] at h
  exact h

theorem egbFixedChargeACritical_pressure_value (w φ : ℝ) :
    egbPressureA (egbFixedChargeACriticalTemperature w φ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeACriticalRadius w φ) = egbFixedChargeACriticalPressure w φ := by
  have h := egbCriticalA_pressure_value (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACritical_pressure_function, egbFixedChargeACriticalLogScale_exp,
    egbFixedChargeACritical_pressure_transfer] at h
  exact h

theorem egbFixedChargeACritical_pressure_inflection (w φ : ℝ) :
    deriv (egbPressureA (egbFixedChargeACriticalTemperature w φ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeACriticalRadius w φ) = 0 ∧
    deriv (deriv (egbPressureA (egbFixedChargeACriticalTemperature w φ) (exp w * cos φ) (exp w * sin φ)))
      (egbFixedChargeACriticalRadius w φ) = 0 := by
  have h := egbCriticalA_pressure_inflection (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACritical_pressure_function, egbFixedChargeACriticalLogScale_exp] at h
  exact h

theorem egbFixedChargeACritical_log_gibbs (w φ l u : ℝ) :
    egbCriticalALogGibbs (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) l u =
      egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (exp u) := by
  unfold egbCriticalALogGibbs
  rw [egbFixedChargeACritical_gibbs_function]

theorem egbFixedChargeACritical_global_minimum (w φ l u : ℝ) :
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeACriticalRadius w φ) ≤
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (exp u) := by
  have h := egbCriticalALogGibbs_global_minimum (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) l u
  simp only [egbFixedChargeACritical_log_gibbs, egbFixedChargeACriticalLogScale_exp] at h
  exact h

theorem egbFixedChargeACritical_unique_minimum (w φ l u : ℝ) :
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (exp u) =
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeACriticalRadius w φ) ↔ exp u = egbFixedChargeACriticalRadius w φ := by
  have h := egbCriticalALogGibbs_unique_minimum (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) l u
  simp only [egbFixedChargeACritical_log_gibbs, egbFixedChargeACriticalLogScale_exp] at h
  have he : exp u = egbFixedChargeACriticalRadius w φ ↔ u = egbFixedChargeACriticalLogScale w φ := by
    rw [← egbFixedChargeACriticalLogScale_exp, exp_eq_exp]
  simpa only [ne_eq, he] using h

theorem egbFixedChargeACritical_strict_gap (w φ l u : ℝ) :
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeACriticalRadius w φ) <
    egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (exp u) ↔ exp u ≠ egbFixedChargeACriticalRadius w φ := by
  have h := egbCriticalALogGibbs_strict_gap (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) l u
  simp only [egbFixedChargeACritical_log_gibbs, egbFixedChargeACriticalLogScale_exp] at h
  have he : exp u = egbFixedChargeACriticalRadius w φ ↔ u = egbFixedChargeACriticalLogScale w φ := by
    rw [← egbFixedChargeACriticalLogScale_exp, exp_eq_exp]
  simpa only [ne_eq, he] using h

def egbFixedChargeACriticalQuarticCoefficient (w φ : ℝ) : ℝ :=
  (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) /
    (12 * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeACritical_quartic_coefficient_transfer (w φ : ℝ) :
    egbCriticalARadialQuarticCoefficient (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) = egbFixedChargeACriticalQuarticCoefficient w φ := by
  unfold egbCriticalARadialQuarticCoefficient egbFixedChargeACriticalQuarticCoefficient
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACriticalAngle_shape]

theorem egbFixedChargeACriticalQuarticCoefficient_pos (w φ : ℝ) :
    0 < egbFixedChargeACriticalQuarticCoefficient w φ := by
  rw [← egbFixedChargeACritical_quartic_coefficient_transfer]
  exact egbCriticalARadialQuarticCoefficient_pos _ _

theorem egbFixedChargeACritical_radial_quartic_limit (w φ l : ℝ) :
    Tendsto (fun r => (egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l r -
      egbOffShellGibbsA (egbFixedChargeACriticalPressure w φ) (egbFixedChargeACriticalTemperature w φ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeACriticalRadius w φ)) / (r - egbFixedChargeACriticalRadius w φ) ^ (4 : ℕ))
      (𝓝[≠] (egbFixedChargeACriticalRadius w φ)) (𝓝 (egbFixedChargeACriticalQuarticCoefficient w φ)) := by
  have h := egbCriticalA_radial_quartic_limit (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) l
  rw [egbFixedChargeACritical_gibbs_function, egbFixedChargeACriticalLogScale_exp,
    egbFixedChargeACritical_quartic_coefficient_transfer] at h
  exact h

end GaloisForLFunctions.HTGeometry
