import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanParameters

/-!
# Actual pressure and temperature in mean-radius coordinates

Exact formulas remove the first-order displacement of either phase radius.
Only the arithmetic mean, squared asymmetry and logarithmic kernel remain.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeA_mean_temperature (w φ τ : ℝ) :
    egbFixedChargeATemperature w φ τ =
      2 / (Real.pi * egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAMeanDenominator τ φ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hD := egbFixedChargeADenominator_pos τ φ
  have hpi := Real.pi_pos
  rw [egbFixedChargeAMeanRadius_formula, egbFixedChargeAMeanDenominator_formula]
  unfold egbFixedChargeATemperature egbFixedChargeATemperatureWeight
  have hz : thermalRatio τ + 1 = 2 / (1 + egbCoexistenceASymmetricRatio τ) := by
    simpa only [add_comm] using egbCoexistenceASymmetricRatio_radius_sum τ
  rw [hz]
  field_simp <;> ring

theorem egbFixedChargeA_mean_pressure (w φ τ : ℝ) :
    egbFixedChargeAPressure w φ τ =
      (3 * (1 + egbCoexistenceASymmetricRatio τ ^ 2) + 2 * egbFixedChargeAMeanCoupling τ φ * (2 - egbCoexistenceALogKernel τ)) /
      (8 * Real.pi * egbFixedChargeAMeanRadius w φ τ ^ 2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hD := egbFixedChargeADenominator_pos τ φ
  have hpi := Real.pi_pos
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  rw [egbFixedChargeAMeanRadius_formula, egbFixedChargeAMeanDenominator_formula, egbFixedChargeAMeanCoupling_formula]
  unfold egbFixedChargeAPressure egbFixedChargeAPressureWeight
  rw [egbCoexistenceASymmetricRatio_square_sum]
  field_simp <;> ring

theorem egbFixedChargeA_mean_pressure_temperature_ratio (w φ τ : ℝ) :
    egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ =
      (3 * (1 + egbCoexistenceASymmetricRatio τ ^ 2) + 2 * egbFixedChargeAMeanCoupling τ φ * (2 - egbCoexistenceALogKernel τ)) /
      (16 * egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hpi := Real.pi_pos
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  rw [egbFixedChargeA_mean_pressure, egbFixedChargeA_mean_temperature]
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
