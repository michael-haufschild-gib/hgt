import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeASecants
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict orientation and actual Clapeyron slope of model-A coexistence

The stable radial responses, strict secant margins and changing radius
ratio force temperature and pressure to decrease strictly. The small
radius decreases while the large radius increases. Consequently the
actual parametric Clapeyron quotient is everywhere defined and positive.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

/-- Temperature cannot stall or reverse along the fixed-charge coexistence curve. -/
theorem egbFixedChargeATemperature_derivative_neg (w φ τ : ℝ) :
    deriv (egbFixedChargeATemperature w φ) τ < 0 := by
  let z := thermalRatio τ
  let R := egbFixedChargeALargeRadius w φ τ
  let A := deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
    (egbFixedChargeASmallRadius w φ τ)
  let B := deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
    (egbFixedChargeALargeRadius w φ τ)
  let JS := egbFixedChargeASmallPressureResponse w φ τ
  let JL := egbFixedChargeALargePressureResponse w φ τ
  let m := egbFixedChargeAClapeyronSlope w φ τ
  let s' := deriv (egbFixedChargeASmallRadius w φ) τ
  let r' := deriv (egbFixedChargeALargeRadius w φ) τ
  let t' := deriv (egbFixedChargeATemperature w φ) τ
  let p' := deriv (egbFixedChargeAPressure w φ) τ
  have hA : 0 < A := egbFixedChargeA_small_thermal_slope_pos w φ τ
  have hB : 0 < B := egbFixedChargeA_large_thermal_slope_pos w φ τ
  have hz : 0 < z := thermalRatio_pos τ
  have hR : 0 < R := egbFixedChargeALargeRadius_pos w φ τ
  have hS : t' = A * s' + JS * p' := egbFixedChargeA_small_equilibrium_derivative w φ τ
  have hL : t' = B * r' + JL * p' := egbFixedChargeA_large_equilibrium_derivative w φ τ
  have hp : p' = m * t' := egbFixedChargeA_pressure_derivative_relation w φ τ
  have hr : s' = (-exp τ * z) * R + z * r' := egbFixedChargeA_radius_derivative_relation w φ τ
  rw [hp] at hS hL
  have hsBound : JS * m < 1 := egbFixedChargeA_small_clapeyron_bound w φ τ
  have hlBound : 1 < JL * m := egbFixedChargeA_large_clapeyron_bound w φ τ
  have hcoef : 0 < B * (1 - JS * m) - z * A * (1 - JL * m) := by
    have h₁ := mul_pos hB (sub_pos.mpr hsBound)
    have h₂ := mul_neg_of_pos_of_neg (mul_pos hz hA) (sub_neg.mpr hlBound)
    linarith
  have hident : (B * (1 - JS * m) - z * A * (1 - JL * m)) * t' = A * B * (-exp τ * z) * R := by
    linear_combination B * hS - z * A * hL + A * B * hr
  have hz' : -exp τ * z < 0 := mul_neg_of_neg_of_pos (by linarith [exp_pos τ]) hz
  have hrhs : A * B * (-exp τ * z) * R < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hA hB) hz') hR
  change t' < 0
  by_contra hn
  have hm := mul_nonneg hcoef.le (le_of_not_gt hn)
  rw [hident] at hm
  exact (not_le_of_gt hrhs) hm

theorem egbFixedChargeAPressure_derivative_neg (w φ τ : ℝ) :
    deriv (egbFixedChargeAPressure w φ) τ < 0 := by
  rw [egbFixedChargeA_pressure_derivative_relation]
  exact mul_neg_of_pos_of_neg (egbFixedChargeAClapeyronSlope_pos w φ τ) (egbFixedChargeATemperature_derivative_neg w φ τ)

theorem egbFixedChargeASmallRadius_derivative_neg (w φ τ : ℝ) :
    deriv (egbFixedChargeASmallRadius w φ) τ < 0 := by
  have h := egbFixedChargeA_small_equilibrium_derivative w φ τ
  rw [egbFixedChargeA_pressure_derivative_relation] at h
  have hA := egbFixedChargeA_small_thermal_slope_pos w φ τ
  have hT := egbFixedChargeATemperature_derivative_neg w φ τ
  have hBound := egbFixedChargeA_small_clapeyron_bound w φ τ
  have he : (deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeASmallRadius w φ τ)) * deriv (egbFixedChargeASmallRadius w φ) τ =
      (1 - (egbFixedChargeASmallPressureResponse w φ τ) * (egbFixedChargeAClapeyronSlope w φ τ)) * deriv (egbFixedChargeATemperature w φ) τ := by
    dsimp only [egbFixedChargeASmallPressureResponse]
    linear_combination -h
  have hm : (deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeASmallRadius w φ τ)) * deriv (egbFixedChargeASmallRadius w φ) τ < 0 := by
    rw [he]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hBound) hT
  by_contra hn
  exact (not_le_of_gt hm) (mul_nonneg hA.le (le_of_not_gt hn))

theorem egbFixedChargeALargeRadius_derivative_pos (w φ τ : ℝ) :
    deriv (egbFixedChargeALargeRadius w φ) τ > 0 := by
  have h := egbFixedChargeA_large_equilibrium_derivative w φ τ
  rw [egbFixedChargeA_pressure_derivative_relation] at h
  have hA := egbFixedChargeA_large_thermal_slope_pos w φ τ
  have hT := egbFixedChargeATemperature_derivative_neg w φ τ
  have hBound := egbFixedChargeA_large_clapeyron_bound w φ τ
  have he : (deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeALargeRadius w φ τ)) * deriv (egbFixedChargeALargeRadius w φ) τ =
      (1 - (egbFixedChargeALargePressureResponse w φ τ) * (egbFixedChargeAClapeyronSlope w φ τ)) * deriv (egbFixedChargeATemperature w φ) τ := by
    dsimp only [egbFixedChargeALargePressureResponse]
    linear_combination -h
  have hm : 0 < (deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeALargeRadius w φ τ)) * deriv (egbFixedChargeALargeRadius w φ) τ := by
    rw [he]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hBound) hT
  exact (mul_pos_iff_of_pos_left hA).1 hm

theorem egbFixedChargeATemperature_strictAnti (w φ : ℝ) : StrictAnti (egbFixedChargeATemperature w φ) :=
  strictAnti_of_deriv_neg (egbFixedChargeATemperature_derivative_neg w φ)

theorem egbFixedChargeAPressure_strictAnti (w φ : ℝ) : StrictAnti (egbFixedChargeAPressure w φ) :=
  strictAnti_of_deriv_neg (egbFixedChargeAPressure_derivative_neg w φ)

theorem egbFixedChargeASmallRadius_strictAnti (w φ : ℝ) : StrictAnti (egbFixedChargeASmallRadius w φ) :=
  strictAnti_of_deriv_neg (egbFixedChargeASmallRadius_derivative_neg w φ)

theorem egbFixedChargeALargeRadius_strictMono (w φ : ℝ) : StrictMono (egbFixedChargeALargeRadius w φ) :=
  strictMono_of_deriv_pos (egbFixedChargeALargeRadius_derivative_pos w φ)

/-- The actual parametric slope equals the entropy jump divided by volume jump. -/
theorem egbFixedChargeA_clapeyron (w φ τ : ℝ) :
    deriv (egbFixedChargeAPressure w φ) τ / deriv (egbFixedChargeATemperature w φ) τ =
      egbFixedChargeAClapeyronSlope w φ τ := by
  have hn := ne_of_lt (egbFixedChargeATemperature_derivative_neg w φ τ)
  rw [egbFixedChargeA_pressure_derivative_relation]
  field_simp

theorem egbFixedChargeA_clapeyron_slope_pos (w φ τ : ℝ) :
    0 < deriv (egbFixedChargeAPressure w φ) τ / deriv (egbFixedChargeATemperature w φ) τ := by
  rw [egbFixedChargeA_clapeyron]
  exact egbFixedChargeAClapeyronSlope_pos w φ τ

end GaloisForLFunctions.HTGeometry
