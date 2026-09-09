import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHeat

/-!
# Exact double-zero factorization on the physical critical isobar

The actual temperature derivative has a squared radius-gap factor at the
critical pressure. Changing pressure adds an explicit affine correction.
This supplies direct algebraic control of the critical heat-capacity pole.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbTemperatureARadialNumerator (P Q a r : ℝ) : ℝ :=
  8 * Real.pi * P * r ^ 6 + 48 * Real.pi * P * a ^ 2 * r ^ 4 - r ^ 4 +
    (2 * a ^ 2 + 3 * (Q ^ 2 + a ^ 2)) * r ^ 2 + 2 * a ^ 2 * (Q ^ 2 + a ^ 2)

theorem egbTemperatureARadialNumerator_pressure_difference (P P₀ Q a r : ℝ) :
    egbTemperatureARadialNumerator P Q a r = egbTemperatureARadialNumerator P₀ Q a r -
      8 * Real.pi * (P₀ - P) * r ^ 4 * (r ^ 2 + 6 * a ^ 2) := by
  unfold egbTemperatureARadialNumerator
  ring

theorem egbFixedChargeACritical_radial_numerator_factorization (w φ r : ℝ) :
    egbTemperatureARadialNumerator (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ) r =
      (r ^ 2 - egbFixedChargeACriticalRadius w φ ^ 2) ^ 2 *
        (8 * Real.pi * egbFixedChargeACriticalPressure w φ * r ^ 2 +
          2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  unfold egbTemperatureARadialNumerator
  rw [egbFixedChargeACritical_charge_scaling, egbFixedChargeACritical_coupling_scaling]
  unfold egbFixedChargeACriticalPressure
  rw [egbFixedChargeACriticalWeight_formula]
  field_simp <;> ring

theorem egbFixedChargeACritical_radial_factor_at_critical (w φ : ℝ) :
    8 * Real.pi * egbFixedChargeACriticalPressure w φ * egbFixedChargeACriticalRadius w φ ^ 2 +
      2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ =
    (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) / 2 := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalPressure
  rw [egbFixedChargeACriticalWeight_formula]
  field_simp <;> ring

theorem egbFixedChargeACritical_radial_factor_pos (w φ u : ℝ) :
    0 < 8 * Real.pi * egbFixedChargeACriticalPressure w φ * exp u ^ 2 +
      2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ := by
  have hp := egbFixedChargeACriticalPressure_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hs := egbFixedChargeACriticalWeight_pos φ
  have hpi := Real.pi_pos
  positivity

theorem egbFixedChargeACritical_radial_slope_factorization (w φ r : ℝ) :
    egbTemperatureARadialSlope (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ) r =
      (r ^ 2 - egbFixedChargeACriticalRadius w φ ^ 2) ^ 2 *
        (8 * Real.pi * egbFixedChargeACriticalPressure w φ * r ^ 2 +
          2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ) /
        (4 * Real.pi * r ^ 2 * (r ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2) := by
  change egbTemperatureARadialNumerator _ _ _ _ / _ = _
  rw [egbFixedChargeACritical_radial_numerator_factorization]

theorem egbFixedChargeACritical_radial_slope_nonneg (w φ u : ℝ) :
    0 ≤ egbTemperatureARadialSlope (egbFixedChargeACriticalPressure w φ) (exp w * cos φ) (exp w * sin φ) (exp u) := by
  rw [egbFixedChargeACritical_radial_slope_factorization]
  have hf := egbFixedChargeACritical_radial_factor_pos w φ u
  have hpi := Real.pi_pos
  positivity

theorem egbFixedChargeA_radial_slope_pressure_decomposition (P w φ u : ℝ) :
    egbTemperatureARadialSlope P (exp w * cos φ) (exp w * sin φ) (exp u) =
      (exp u ^ 2 - egbFixedChargeACriticalRadius w φ ^ 2) ^ 2 *
        (8 * Real.pi * egbFixedChargeACriticalPressure w φ * exp u ^ 2 +
          2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ) /
        (4 * Real.pi * exp u ^ 2 * (exp u ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2) -
      (egbFixedChargeACriticalPressure w φ - P) *
        (2 * exp u ^ 2 * (exp u ^ 2 + 6 * (exp w * sin φ) ^ 2) / (exp u ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2) := by
  have hu := exp_pos u
  have hpi := Real.pi_pos
  have hden : 0 < exp u ^ 2 + 2 * (exp w * sin φ) ^ 2 := by positivity
  change egbTemperatureARadialNumerator _ _ _ _ / _ = _
  rw [egbTemperatureARadialNumerator_pressure_difference P (egbFixedChargeACriticalPressure w φ),
    egbFixedChargeACritical_radial_numerator_factorization]
  field_simp <;> ring

theorem egbFixedChargeACritical_heat_numerator_value (w φ : ℝ) :
    egbFixedChargeACriticalHeatNumerator w φ = 2 / 3 := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalHeatNumerator egbFixedChargeACriticalTemperature
  rw [egbFixedChargeACritical_coupling_scaling]
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
