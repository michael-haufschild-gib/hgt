import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitCriticalLimit
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalJumpExponents
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanHeatAmplitude

/-!
# Physical observable rates of the sixth-order mean deficit

The deficit is cubic in temperature and pressure gaps and sixth order
in phase jumps. Its products with cubed phase heat capacities have equal
positive limits; the mean heat capacity gives minus eight times that limit.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanGibbsDeficit_temperature_cubic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) ^ (3 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ / (egbFixedChargeATemperatureGapCoefficient w φ) ^ (3 : ℕ))) := by
  have hp := egbFixedChargeATemperatureGapCoefficient_pos w φ
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeATemperatureGap_quadratic_critical_limit w φ).pow 3) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_pressure_cubic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) ^ (3 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ / (egbFixedChargeAPressureGapCoefficient w φ) ^ (3 : ℕ))) := by
  have hp := egbFixedChargeAPressureGapCoefficient_pos w φ
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeAPressureGap_quadratic_critical_limit w φ).pow 3) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_radius_sixth_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / (egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) ^ (6 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ / (2 * egbFixedChargeACriticalRadius w φ) ^ (6 : ℕ))) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeA_radius_gap_asymmetry_limit w φ).pow 6) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_entropy_sixth_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / (egbFixedChargeAEntropyJump w φ τ) ^ (6 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ / (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) ^ (6 : ℕ))) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hp := Real.pi_pos
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeA_entropy_asymmetry_critical_limit w φ).pow 6) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_volume_sixth_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / (egbFixedChargeAVolumeJump w φ τ) ^ (6 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ / (8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ)) ^ (6 : ℕ))) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hp := Real.pi_pos
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeA_volume_asymmetry_critical_limit w φ).pow 6) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_latent_heat_sixth_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / (egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) ^ (6 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ / (4 * egbFixedChargeACriticalRadius w φ / 3) ^ (6 : ℕ))) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).div
    ((egbFixedChargeA_latent_heat_asymmetry_critical_limit w φ).pow 6) (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_small_heat_cubed_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l₁ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeASmallRadius w φ τ) ^ (3 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ * egbFixedChargeACriticalHeatAmplitude w φ ^ (3 : ℕ))) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l₁).mul
    ((egbFixedChargeA_small_heat_capacity_amplitude w φ l₂).pow 3)
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAMeanGibbsDeficit_large_heat_cubed_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l₁ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeALargeRadius w φ τ) ^ (3 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ * egbFixedChargeACriticalHeatAmplitude w φ ^ (3 : ℕ))) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l₁).mul
    ((egbFixedChargeA_large_heat_capacity_amplitude w φ l₂).pow 3)
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAMeanGibbsDeficit_mean_heat_cubed_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l₁ *
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂
        (egbFixedChargeAMeanRadius w φ τ) ^ (3 : ℕ))
      atBot (𝓝 (-8 * egbFixedChargeAMeanDeficitCoefficient w φ * egbFixedChargeACriticalHeatAmplitude w φ ^ (3 : ℕ))) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l₁).mul
    ((egbFixedChargeA_mean_heat_capacity_amplitude w φ l₂).pow 3)
  have he : egbFixedChargeAMeanDeficitCoefficient w φ * (-2 * egbFixedChargeACriticalHeatAmplitude w φ) ^ (3 : ℕ) =
      -8 * egbFixedChargeAMeanDeficitCoefficient w φ * egbFixedChargeACriticalHeatAmplitude w φ ^ (3 : ℕ) := by ring
  rw [he] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
