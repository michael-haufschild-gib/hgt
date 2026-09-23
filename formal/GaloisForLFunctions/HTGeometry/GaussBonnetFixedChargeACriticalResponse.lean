import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalStates
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeATangents

/-!
# Actual thermal response at the fixed-charge critical endpoint

The physical radial temperature derivative vanishes at the matched
critical state. The pressure derivative remains positive and its inverse
is exactly the limiting coexistence Clapeyron slope.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeACritical_coupling_scaling (w φ : ℝ) :
    (exp w * sin φ) ^ (2 : ℕ) = egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * egbFixedChargeACriticalCouplingWeight φ := by
  have h := egbCriticalA_coupling_square (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACritical_coupling_square, egbFixedChargeACriticalLogScale_exp,
    egbFixedChargeACriticalAngle_shape] at h
  exact h

theorem egbFixedChargeACritical_charge_scaling (w φ : ℝ) :
    (exp w * cos φ) ^ (2 : ℕ) + (exp w * sin φ) ^ (2 : ℕ) =
      egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * egbFixedChargeACriticalWeight φ := by
  rw [egbFixedChargeA_conserved_scale, egbFixedChargeACritical_effective_scale]

theorem egbFixedChargeACritical_radial_slope_zero (w φ : ℝ) :
    egbTemperatureARadialSlope (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeACriticalRadius w φ) = 0 := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbTemperatureARadialSlope
  rw [egbFixedChargeACritical_charge_scaling, egbFixedChargeACritical_coupling_scaling,
    egbFixedChargeACriticalWeight_formula]
  unfold egbFixedChargeACriticalPressure
  field_simp
  ring

theorem egbFixedChargeACritical_temperature_derivative_zero (w φ : ℝ) :
    deriv (egbTemperatureA (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeACriticalRadius w φ) = 0 := by
  have h := (egbTemperatureA_hasDerivAt (egbFixedChargeACriticalPressure w φ) (exp w * cos φ)
    (exp w * sin φ) (egbFixedChargeACriticalLogScale w φ)).deriv
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACritical_radial_slope_zero] at h
  exact h

theorem egbFixedChargeACritical_pressure_response (w φ : ℝ) :
    egbThermalPressureResponseA (exp w * sin φ) (egbFixedChargeACriticalRadius w φ) =
      2 * egbFixedChargeACriticalRadius w φ / (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) := by
  have hR := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbThermalPressureResponseA
  rw [egbFixedChargeACritical_coupling_scaling]
  field_simp

theorem egbFixedChargeACritical_pressure_derivative (w φ : ℝ) :
    deriv (fun P => egbTemperatureA P (exp w * cos φ) (exp w * sin φ) (egbFixedChargeACriticalRadius w φ))
      (egbFixedChargeACriticalPressure w φ) =
        2 * egbFixedChargeACriticalRadius w φ / (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) := by
  have h := (egbTemperatureA_pressure_hasDerivAt (egbFixedChargeACriticalPressure w φ) (exp w * cos φ)
    (exp w * sin φ) (egbFixedChargeACriticalLogScale w φ)).deriv
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACritical_pressure_response] at h
  exact h

theorem egbFixedChargeACritical_inverse_pressure_response (w φ : ℝ) :
    (egbThermalPressureResponseA (exp w * sin φ) (egbFixedChargeACriticalRadius w φ))⁻¹ =
      (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ) := by
  rw [egbFixedChargeACritical_pressure_response, inv_div]

end GaloisForLFunctions.HTGeometry
