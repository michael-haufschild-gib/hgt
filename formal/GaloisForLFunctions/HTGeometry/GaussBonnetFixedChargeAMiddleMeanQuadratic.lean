import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleMeanParameters

/-!
# Actual middle-root quadratic after recentering the phase radii
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeAPressureWeight_mean_formula (τ φ : ℝ) :
    egbFixedChargeAPressureWeight τ φ =
      egbFixedChargeAMeanPressureNumerator τ φ * (1 + egbCoexistenceASymmetricRatio τ) ^ 2 /
        (egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hD := egbFixedChargeADenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  rw [egbFixedChargeAMeanDenominator_formula]
  unfold egbFixedChargeAPressureWeight egbFixedChargeAMeanPressureNumerator
  rw [egbCoexistenceASymmetricRatio_square_sum, egbFixedChargeAMeanCoupling_formula]
  field_simp <;> ring

theorem egbFixedChargeATemperatureWeight_mean_formula (τ φ : ℝ) :
    egbFixedChargeATemperatureWeight τ φ = 8 * (1 + egbCoexistenceASymmetricRatio τ) / egbFixedChargeAMeanDenominator τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hD := egbFixedChargeADenominator_pos τ φ
  rw [egbFixedChargeAMeanDenominator_formula]
  unfold egbFixedChargeATemperatureWeight
  have hz : thermalRatio τ + 1 = 2 / (1 + egbCoexistenceASymmetricRatio τ) := by
    simpa only [add_comm] using egbCoexistenceASymmetricRatio_radius_sum τ
  rw [hz]
  field_simp <;> ring

theorem egbFixedChargeAMeanPressureNumerator_pos (τ φ : ℝ) : 0 < egbFixedChargeAMeanPressureNumerator τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hp : 0 < egbFixedChargeAPressureWeight τ φ := by
    rw [← egbFixedChargeAAngle_pressure_weight]
    exact egbCoexistenceAPressureWeight_pos τ (egbFixedChargeAAngle τ φ)
  have he : egbFixedChargeAMeanPressureNumerator τ φ =
      egbFixedChargeAPressureWeight τ φ * (egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) /
        (1 + egbCoexistenceASymmetricRatio τ) ^ 2 := by
    rw [egbFixedChargeAPressureWeight_mean_formula]
    have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
    field_simp
  rw [he]
  positivity

theorem egbFixedChargeAStationaryLinear_mean_formula (τ φ : ℝ) :
    egbCoexistenceAStationaryLinear τ (egbFixedChargeAAngle τ φ) =
      (1 + egbCoexistenceASymmetricRatio τ) * egbFixedChargeAMiddleMeanLinear τ φ /
        (egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  unfold egbCoexistenceAStationaryLinear egbFixedChargeAMiddleMeanLinear
  rw [egbFixedChargeAAngle_pressure_weight, egbFixedChargeAAngle_temperature_weight,
    egbFixedChargeAPressureWeight_mean_formula, egbFixedChargeATemperatureWeight_mean_formula]
  have hz : thermalRatio τ + 1 = 2 / (1 + egbCoexistenceASymmetricRatio τ) := by
    simpa only [add_comm] using egbCoexistenceASymmetricRatio_radius_sum τ
  rw [hz]
  field_simp <;> ring

theorem egbFixedChargeAStationaryConstant_mean_formula (τ φ : ℝ) :
    egbFixedChargeAWeight τ φ / thermalRatio τ =
      egbFixedChargeAMeanWeight τ φ / (1 - egbCoexistenceASymmetricRatio τ ^ 2) := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have h1 : 0 < 1 - egbCoexistenceASymmetricRatio τ := by linarith [hd.2]
  have h2 : 0 < 1 + egbCoexistenceASymmetricRatio τ := by linarith [hd.1]
  have hx : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 := by nlinarith [hd.1, hd.2]
  unfold egbFixedChargeAMeanWeight
  rw [egbCoexistenceASymmetricRatio_inversion]
  field_simp <;> ring

theorem egbFixedChargeAMiddleMeanRatio_quadratic (τ φ : ℝ) :
    egbFixedChargeAMeanPressureNumerator τ φ * egbFixedChargeAMiddleMeanRatio τ φ ^ 2 +
      egbFixedChargeAMiddleMeanLinear τ φ * egbFixedChargeAMiddleMeanRatio τ φ + egbFixedChargeAMiddleMeanConstant τ φ = 0 := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 := by nlinarith [hd.1, hd.2]
  have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  have h := egbCoexistenceAMiddleRadius_quadratic τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeAAngle_pressure_weight, egbFixedChargeAPressureWeight_mean_formula,
    egbFixedChargeAStationaryLinear_mean_formula, egbFixedChargeAAngle_charge_weight,
    egbFixedChargeAStationaryConstant_mean_formula] at h
  unfold egbFixedChargeAMiddleMeanRatio egbFixedChargeAMiddleMeanConstant
  have he : egbFixedChargeAMeanPressureNumerator τ φ * ((1 + egbCoexistenceASymmetricRatio τ) * egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)) ^ 2 +
      egbFixedChargeAMiddleMeanLinear τ φ * ((1 + egbCoexistenceASymmetricRatio τ) * egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)) +
      (-egbFixedChargeAMeanWeight τ φ * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) / (1 - egbCoexistenceASymmetricRatio τ ^ 2)) =
      (egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) *
        (egbFixedChargeAMeanPressureNumerator τ φ * (1 + egbCoexistenceASymmetricRatio τ) ^ 2 /
          (egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) * egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ) ^ 2 +
        (1 + egbCoexistenceASymmetricRatio τ) * egbFixedChargeAMiddleMeanLinear τ φ /
          (egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2)) * egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ) -
          egbFixedChargeAMeanWeight τ φ / (1 - egbCoexistenceASymmetricRatio τ ^ 2)) := by
    field_simp <;> ring
  rw [he, h, mul_zero]

end GaloisForLFunctions.HTGeometry
