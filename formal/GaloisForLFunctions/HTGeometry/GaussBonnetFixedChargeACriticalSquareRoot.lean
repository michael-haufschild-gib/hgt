import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPressureGapRate
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeARanges

/-!
# Physical square-root critical phase separation

Temperature and pressure gaps vanish quadratically in the symmetric
radius asymmetry, while the phase-radius gap vanishes linearly. Exact
positive amplitudes give both physical square-root laws and the endpoint
pressure-temperature secant slope.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeA_temperature_gap_sqrt_normalization (w φ τ : ℝ) :
    sqrt ((egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) =
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ := by
  have hg := sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ)
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [sqrt_div hg.le, sqrt_sq hd.le]

theorem egbFixedChargeA_pressure_gap_sqrt_normalization (w φ τ : ℝ) :
    sqrt ((egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) =
      sqrt (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) / egbCoexistenceASymmetricRatio τ := by
  have hg := sub_pos.mpr (egbFixedChargeAPressure_below_critical w φ τ)
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [sqrt_div hg.le, sqrt_sq hd.le]

theorem egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit (w φ : ℝ) :
    Tendsto (fun τ => sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  simpa only [egbFixedChargeA_temperature_gap_sqrt_normalization] using
    (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ).sqrt

theorem egbFixedChargeA_pressure_gap_sqrt_asymmetry_limit (w φ : ℝ) :
    Tendsto (fun τ => sqrt (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (sqrt (egbFixedChargeAPressureGapCoefficient w φ))) := by
  simpa only [egbFixedChargeA_pressure_gap_sqrt_normalization] using
    (egbFixedChargeAPressureGap_quadratic_critical_limit w φ).sqrt

theorem egbFixedChargeA_radius_gap_temperature_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) /
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (2 * egbFixedChargeACriticalRadius w φ / sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeATemperatureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_radius_gap_asymmetry_limit w φ).div (egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_radius_gap_pressure_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) /
      sqrt (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 (2 * egbFixedChargeACriticalRadius w φ / sqrt (egbFixedChargeAPressureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeAPressureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_radius_gap_asymmetry_limit w φ).div (egbFixedChargeA_pressure_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeAPressure_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_large_radius_temperature_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeALargeRadius w φ τ - egbFixedChargeACriticalRadius w φ) /
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ / sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeATemperatureGapCoefficient_pos w φ)
  have h := (egbFixedChargeALargeRadius_linear_critical_limit w φ).div (egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_small_radius_temperature_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeASmallRadius w φ τ - egbFixedChargeACriticalRadius w φ) /
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (-egbFixedChargeACriticalRadius w φ / sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeATemperatureGapCoefficient_pos w φ)
  have h := (egbFixedChargeASmallRadius_linear_critical_limit w φ).div (egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_critical_gap_amplitude_ratio (w φ : ℝ) :
    egbFixedChargeAPressureGapCoefficient w φ / egbFixedChargeATemperatureGapCoefficient w φ =
      (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  unfold egbFixedChargeAPressureGapCoefficient egbFixedChargeATemperatureGapCoefficient egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeA_critical_pressure_temperature_gap_ratio (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) /
      (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) / (2 * egbFixedChargeACriticalRadius w φ))) := by
  have h := (egbFixedChargeAPressureGap_quadratic_critical_limit w φ).div
    (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ) (egbFixedChargeATemperatureGapCoefficient_pos w φ).ne'
  rw [egbFixedChargeA_critical_gap_amplitude_ratio] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ)
  field_simp

end GaloisForLFunctions.HTGeometry
