import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdWeights
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAParameters
import Mathlib.Topology.Algebra.Order.Field

/-!
# Actual cold endpoint and universal scaling of model-A coexistence

The small phase approaches the fixed extremal radius while the large
phase diverges. Actual temperature and pressure vanish. Their normalized
limits yield the universal law P/T² → 3π/8, independent of charge fraction
and Gauss–Bonnet coupling fraction.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeA_sqrt_weight_normalized (τ φ : ℝ) :
    sqrt (egbFixedChargeAWeight τ φ) = sqrt (egbFixedChargeANormalizedWeight τ φ) * thermalRatio τ := by
  rw [egbFixedChargeAWeight_normalized, sqrt_mul (egbFixedChargeANormalizedWeight_pos τ φ).le,
    sqrt_sq_eq_abs, abs_of_pos (thermalRatio_pos τ)]

theorem egbFixedChargeASmallRadius_normalized (w φ τ : ℝ) :
    egbFixedChargeASmallRadius w φ τ = exp w / sqrt (egbFixedChargeANormalizedWeight τ φ) := by
  have hz := thermalRatio_pos τ
  have hn := egbFixedChargeANormalizedWeight_pos τ φ
  unfold egbFixedChargeASmallRadius egbFixedChargeALargeRadius
  rw [egbFixedChargeA_sqrt_weight_normalized]
  field_simp <;> ring

theorem egbFixedChargeASmallRadius_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeASmallRadius w φ) atTop (𝓝 (exp w)) := by
  change Tendsto (fun τ => egbFixedChargeASmallRadius w φ τ) atTop (𝓝 (exp w))
  simp only [egbFixedChargeASmallRadius_normalized]
  have h := (tendsto_const_nhds (x := exp w)).div (egbFixedChargeANormalizedWeight_cold_limit φ).sqrt
    (show sqrt (1 : ℝ) ≠ 0 by simp)
  simpa only [Pi.div_def, sqrt_one, div_one] using h

/-- The large phase diverges even though the small phase has a finite cold limit. -/
theorem egbFixedChargeALargeRadius_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeALargeRadius w φ) atTop atTop := by
  change Tendsto (fun τ => exp w / sqrt (egbFixedChargeAWeight τ φ)) atTop atTop
  have hs : Tendsto (fun τ => sqrt (egbFixedChargeAWeight τ φ)) atTop (𝓝 0) := by
    simpa only [sqrt_zero] using (egbFixedChargeAWeight_cold_limit φ).sqrt
  have hsRight : Tendsto (fun τ => sqrt (egbFixedChargeAWeight τ φ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs, Filter.Eventually.of_forall
      (fun τ => sqrt_pos.mpr (egbFixedChargeAWeight_pos τ φ))⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hsRight
  have h := Filter.Tendsto.pos_mul_atTop (exp_pos w) (tendsto_const_nhds (x := exp w)) hinv
  simpa only [egbFixedChargeALargeRadius, Function.comp_def, div_eq_mul_inv] using h

theorem egbFixedChargeATemperature_scale (w φ τ : ℝ) :
    egbFixedChargeATemperature w φ τ =
      egbFixedChargeATemperatureWeight τ φ * sqrt (egbFixedChargeAWeight τ φ) / (4 * Real.pi * exp w) := by
  have hs := egbFixedChargeAWeight_pos τ φ
  unfold egbFixedChargeATemperature egbFixedChargeALargeRadius
  field_simp <;> ring

theorem egbFixedChargeAPressure_scale (w φ τ : ℝ) :
    egbFixedChargeAPressure w φ τ =
      egbFixedChargeAPressureWeight τ φ * egbFixedChargeAWeight τ φ / (8 * Real.pi * exp w ^ 2) := by
  have hs := egbFixedChargeAWeight_pos τ φ
  unfold egbFixedChargeAPressure egbFixedChargeALargeRadius
  rw [div_pow, sq_sqrt hs.le]
  field_simp <;> ring

theorem egbFixedChargeATemperature_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeATemperature w φ) atTop (𝓝 0) := by
  change Tendsto (fun τ => egbFixedChargeATemperature w φ τ) atTop (𝓝 0)
  simp only [egbFixedChargeATemperature_scale]
  have h : Tendsto (fun τ => egbFixedChargeATemperatureWeight τ φ * sqrt (egbFixedChargeAWeight τ φ) /
      (4 * Real.pi * exp w)) atTop (𝓝 ((4 * sqrt 0) / (4 * Real.pi * exp w))) :=
    ((egbFixedChargeATemperatureWeight_cold_limit φ).mul (egbFixedChargeAWeight_cold_limit φ).sqrt).div
      tendsto_const_nhds (by positivity)
  simpa only [sqrt_zero, mul_zero, zero_div] using h

theorem egbFixedChargeAPressure_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAPressure w φ) atTop (𝓝 0) := by
  change Tendsto (fun τ => egbFixedChargeAPressure w φ τ) atTop (𝓝 0)
  simp only [egbFixedChargeAPressure_scale]
  have h : Tendsto (fun τ => egbFixedChargeAPressureWeight τ φ * egbFixedChargeAWeight τ φ /
      (8 * Real.pi * exp w ^ 2)) atTop (𝓝 ((3 * 0) / (8 * Real.pi * exp w ^ 2))) :=
    ((egbFixedChargeAPressureWeight_cold_limit φ).mul (egbFixedChargeAWeight_cold_limit φ)).div
      tendsto_const_nhds (by positivity)
  simpa only [mul_zero, zero_div] using h

theorem egbFixedChargeATemperature_radius_product (w φ τ : ℝ) :
    egbFixedChargeATemperature w φ τ * egbFixedChargeALargeRadius w φ τ = egbFixedChargeATemperatureWeight τ φ / (4 * Real.pi) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbFixedChargeATemperature
  field_simp <;> ring

theorem egbFixedChargeAPressure_radius_product (w φ τ : ℝ) :
    egbFixedChargeAPressure w φ τ * egbFixedChargeALargeRadius w φ τ ^ 2 = egbFixedChargeAPressureWeight τ φ / (8 * Real.pi) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbFixedChargeAPressure
  field_simp <;> ring

theorem egbFixedChargeATemperature_radius_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ * egbFixedChargeALargeRadius w φ τ) atTop (𝓝 (1 / Real.pi)) := by
  simp only [egbFixedChargeATemperature_radius_product]
  have h : Tendsto (fun τ => egbFixedChargeATemperatureWeight τ φ / (4 * Real.pi)) atTop (𝓝 (4 / (4 * Real.pi))) :=
    (egbFixedChargeATemperatureWeight_cold_limit φ).div tendsto_const_nhds (by positivity)
  have he : (4 : ℝ) / (4 * Real.pi) = 1 / Real.pi := by field_simp
  rwa [he] at h

theorem egbFixedChargeAPressure_radius_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPressure w φ τ * egbFixedChargeALargeRadius w φ τ ^ 2) atTop (𝓝 (3 / (8 * Real.pi))) := by
  simp only [egbFixedChargeAPressure_radius_product]
  exact (egbFixedChargeAPressureWeight_cold_limit φ).div tendsto_const_nhds (by positivity)

theorem egbFixedChargeA_pressure_temperature_ratio (w φ τ : ℝ) :
    egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ ^ 2 =
      2 * Real.pi * egbFixedChargeAPressureWeight τ φ / egbFixedChargeATemperatureWeight τ φ ^ 2 := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have ht := egbFixedChargeATemperatureWeight_pos τ φ
  unfold egbFixedChargeAPressure egbFixedChargeATemperature
  field_simp <;> ring

/-- A universal cold equation-of-state coefficient for every fixed charge/coupling fraction. -/
theorem egbFixedChargeA_pressure_temperature_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ ^ 2) atTop (𝓝 (3 * Real.pi / 8)) := by
  simp only [egbFixedChargeA_pressure_temperature_ratio]
  have h : Tendsto (fun τ => 2 * Real.pi * egbFixedChargeAPressureWeight τ φ / egbFixedChargeATemperatureWeight τ φ ^ 2)
      atTop (𝓝 ((2 * Real.pi * 3) / (4 : ℝ) ^ 2)) :=
    (tendsto_const_nhds.mul (egbFixedChargeAPressureWeight_cold_limit φ)).div
      ((egbFixedChargeATemperatureWeight_cold_limit φ).pow 2) (by norm_num)
  have he : (2 * Real.pi * 3) / (4 : ℝ) ^ 2 = 3 * Real.pi / 8 := by ring
  rwa [he] at h

end GaloisForLFunctions.HTGeometry
