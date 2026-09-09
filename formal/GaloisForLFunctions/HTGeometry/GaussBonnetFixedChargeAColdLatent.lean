import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdEntropy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMonotonicity

/-!
# Divergent cold latent heat and the vanishing coexistence tangent

Actual entropy and volume discontinuities diverge. Their quotient tends
to zero with an explicit temperature-normalized limit. The latent heat,
although temperature vanishes, grows linearly with the large radius.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeALatentHeat (w φ τ : ℝ) : ℝ :=
  egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ

theorem egbFixedChargeALargeRadius_square_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeALargeRadius w φ τ ^ 2) atTop atTop :=
  (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp (egbFixedChargeALargeRadius_cold_limit w φ)

theorem egbFixedChargeALargeRadius_cube_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeALargeRadius w φ τ ^ 3) atTop atTop :=
  (tendsto_pow_atTop (show (3 : ℕ) ≠ 0 by norm_num)).comp (egbFixedChargeALargeRadius_cold_limit w φ)

theorem egbFixedChargeAEntropyJump_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAEntropyJump w φ) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop Real.pi_pos
    (egbFixedChargeAEntropyJump_radius_square_cold_limit w φ) (egbFixedChargeALargeRadius_square_cold_limit w φ)
  have he : (fun τ => (egbFixedChargeAEntropyJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ 2) *
      egbFixedChargeALargeRadius w φ τ ^ 2) = egbFixedChargeAEntropyJump w φ := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

theorem egbFixedChargeAVolumeJump_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAVolumeJump w φ) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (show 0 < 4 * Real.pi / 3 by positivity)
    (egbFixedChargeAVolumeJump_radius_cube_cold_limit w φ) (egbFixedChargeALargeRadius_cube_cold_limit w φ)
  have he : (fun τ => (egbFixedChargeAVolumeJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ 3) *
      egbFixedChargeALargeRadius w φ τ ^ 3) = egbFixedChargeAVolumeJump w φ := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

theorem egbFixedChargeAClapeyronSlope_temperature_formula (w φ τ : ℝ) :
    egbFixedChargeAClapeyronSlope w φ τ / egbFixedChargeATemperature w φ τ =
      3 * Real.pi * egbFixedChargeAEntropyWeight τ φ /
        (egbFixedChargeATemperatureWeight τ φ * (1 - thermalRatio τ ^ 3)) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbFixedChargeAClapeyronSlope egbFixedChargeATemperature
  rw [egbFixedChargeAEntropyJump_weight, egbFixedChargeAVolumeJump_formula]
  field_simp <;> ring

theorem egbFixedChargeAClapeyronSlope_temperature_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAClapeyronSlope w φ τ / egbFixedChargeATemperature w φ τ) atTop
      (𝓝 (3 * Real.pi / 4)) := by
  simp only [egbFixedChargeAClapeyronSlope_temperature_formula]
  have h : Tendsto (fun τ => 3 * Real.pi * egbFixedChargeAEntropyWeight τ φ /
      (egbFixedChargeATemperatureWeight τ φ * (1 - thermalRatio τ ^ 3))) atTop
      (𝓝 ((3 * Real.pi * 1) / (4 * (1 - (0 : ℝ) ^ 3)))) :=
    (tendsto_const_nhds.mul (egbFixedChargeAEntropyWeight_cold_limit φ)).div
      ((egbFixedChargeATemperatureWeight_cold_limit φ).mul (tendsto_const_nhds.sub (thermalRatio_tendsto_atTop_zero.pow 3))) (by norm_num)
  norm_num at h
  exact h

theorem egbFixedChargeAClapeyronSlope_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAClapeyronSlope w φ) atTop (𝓝 0) := by
  have h := (egbFixedChargeAClapeyronSlope_temperature_cold_limit w φ).mul (egbFixedChargeATemperature_cold_limit w φ)
  have he : (fun τ => (egbFixedChargeAClapeyronSlope w φ τ / egbFixedChargeATemperature w φ τ) *
      egbFixedChargeATemperature w φ τ) = egbFixedChargeAClapeyronSlope w φ := by
    funext τ
    have hT := egbFixedChargeATemperature_pos w φ τ
    field_simp
  rw [he] at h
  simpa only [mul_zero] using h

theorem egbFixedChargeA_actual_slope_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbFixedChargeAPressure w φ) τ / deriv (egbFixedChargeATemperature w φ) τ) atTop (𝓝 0) := by
  simp only [egbFixedChargeA_clapeyron]
  exact egbFixedChargeAClapeyronSlope_cold_limit w φ

theorem egbFixedChargeA_actual_slope_temperature_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => (deriv (egbFixedChargeAPressure w φ) τ / deriv (egbFixedChargeATemperature w φ) τ) /
      egbFixedChargeATemperature w φ τ) atTop (𝓝 (3 * Real.pi / 4)) := by
  simp only [egbFixedChargeA_clapeyron]
  exact egbFixedChargeAClapeyronSlope_temperature_cold_limit w φ

theorem egbFixedChargeALatentHeat_pos (w φ τ : ℝ) : 0 < egbFixedChargeALatentHeat w φ τ :=
  mul_pos (egbFixedChargeATemperature_pos w φ τ) (egbFixedChargeAEntropyJump_pos w φ τ)

theorem egbFixedChargeALatentHeat_enthalpy (w φ τ : ℝ) :
    egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) =
        egbFixedChargeALatentHeat w φ τ := egbFixedChargeA_enthalpy_jump w φ τ

theorem egbFixedChargeALatentHeat_radius_formula (w φ τ : ℝ) :
    egbFixedChargeALatentHeat w φ τ / egbFixedChargeALargeRadius w φ τ =
      (egbFixedChargeATemperature w φ τ * egbFixedChargeALargeRadius w φ τ) *
        (egbFixedChargeAEntropyJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ 2) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbFixedChargeALatentHeat
  field_simp <;> ring

theorem egbFixedChargeALatentHeat_radius_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeALatentHeat w φ τ / egbFixedChargeALargeRadius w φ τ) atTop (𝓝 1) := by
  simp only [egbFixedChargeALatentHeat_radius_formula]
  have h := (egbFixedChargeATemperature_radius_cold_limit w φ).mul (egbFixedChargeAEntropyJump_radius_square_cold_limit w φ)
  simpa only [one_div, inv_mul_cancel₀ Real.pi_ne_zero] using h

/-- Vanishing temperature coexists with unbounded latent heat because the entropy jump grows faster. -/
theorem egbFixedChargeALatentHeat_cold_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeALatentHeat w φ) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (show (0 : ℝ) < 1 by norm_num)
    (egbFixedChargeALatentHeat_radius_cold_limit w φ) (egbFixedChargeALargeRadius_cold_limit w φ)
  have he : (fun τ => (egbFixedChargeALatentHeat w φ τ / egbFixedChargeALargeRadius w φ τ) *
      egbFixedChargeALargeRadius w φ τ) = egbFixedChargeALatentHeat w φ := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    field_simp
  rwa [he] at h

theorem egbFixedChargeA_enthalpy_jump_cold_limit (w φ : ℝ) :
    Tendsto (fun τ =>
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) -
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)) atTop atTop := by
  simp only [egbFixedChargeALatentHeat_enthalpy]
  exact egbFixedChargeALatentHeat_cold_limit w φ

end GaloisForLFunctions.HTGeometry
