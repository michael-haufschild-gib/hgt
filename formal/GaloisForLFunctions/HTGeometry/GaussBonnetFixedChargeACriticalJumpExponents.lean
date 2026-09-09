import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSquareRoot
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalGapScaling

/-!
# Square-root critical laws for entropy, volume and latent heat

The same physical exponent governs the three phase jumps. Each amplitude
is explicit and positive. These statements concern the actual conserved-
charge coexistence family, including the logarithmic entropy contribution.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbFixedChargeA_entropy_asymmetry_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAEntropyJump w φ τ) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have h := (egbFixedChargeAEntropyJump_scaled_critical_limit w φ).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add thermalRatio_tendsto_atBot_one)
  convert h using 1
  · funext τ
    have hz := thermalRatio_pos τ
    have h1 := sub_pos.mpr (thermalRatio_lt_one τ)
    unfold egbCoexistenceASymmetricRatio
    field_simp <;> ring
  · ring

theorem egbFixedChargeA_volume_asymmetry_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAVolumeJump w φ τ) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 3)) := by
  have h := (egbFixedChargeAVolumeJump_scaled_critical_limit w φ).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add thermalRatio_tendsto_atBot_one)
  convert h using 1
  · funext τ
    have hz := thermalRatio_pos τ
    have h1 := sub_pos.mpr (thermalRatio_lt_one τ)
    unfold egbCoexistenceASymmetricRatio
    field_simp <;> ring
  · ring

theorem egbFixedChargeA_latent_heat_asymmetry_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (4 * egbFixedChargeACriticalRadius w φ / 3)) := by
  have h := (egbFixedChargeA_latent_heat_scaled_critical_limit w φ).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add thermalRatio_tendsto_atBot_one)
  convert h using 1
  · funext τ
    have hz := thermalRatio_pos τ
    have h1 := sub_pos.mpr (thermalRatio_lt_one τ)
    unfold egbCoexistenceASymmetricRatio
    field_simp <;> ring
  · ring

theorem egbFixedChargeA_entropy_temperature_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAEntropyJump w φ τ) /
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 ((4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) / sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeATemperatureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_entropy_asymmetry_critical_limit w φ).div
    (egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_volume_temperature_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAVolumeJump w φ τ) /
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 ((8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 3) / sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeATemperatureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_volume_asymmetry_critical_limit w φ).div
    (egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_latent_heat_temperature_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) /
      sqrt (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 ((4 * egbFixedChargeACriticalRadius w φ / 3) / sqrt (egbFixedChargeATemperatureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeATemperatureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_latent_heat_asymmetry_critical_limit w φ).div
    (egbFixedChargeA_temperature_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_entropy_pressure_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAEntropyJump w φ τ) /
      sqrt (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 ((4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) / sqrt (egbFixedChargeAPressureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeAPressureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_entropy_asymmetry_critical_limit w φ).div
    (egbFixedChargeA_pressure_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeAPressure_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_volume_pressure_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAVolumeJump w φ τ) /
      sqrt (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 ((8 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 3) / sqrt (egbFixedChargeAPressureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeAPressureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_volume_asymmetry_critical_limit w φ).div
    (egbFixedChargeA_pressure_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeAPressure_below_critical w φ τ))
  field_simp

theorem egbFixedChargeA_latent_heat_pressure_square_root_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeATemperature w φ τ * egbFixedChargeAEntropyJump w φ τ) /
      sqrt (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 ((4 * egbFixedChargeACriticalRadius w φ / 3) / sqrt (egbFixedChargeAPressureGapCoefficient w φ))) := by
  have hc := sqrt_pos.mpr (egbFixedChargeAPressureGapCoefficient_pos w φ)
  have h := (egbFixedChargeA_latent_heat_asymmetry_critical_limit w φ).div
    (egbFixedChargeA_pressure_gap_sqrt_asymmetry_limit w φ) hc.ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hg := sqrt_pos.mpr (sub_pos.mpr (egbFixedChargeAPressure_below_critical w φ τ))
  field_simp

end GaloisForLFunctions.HTGeometry
