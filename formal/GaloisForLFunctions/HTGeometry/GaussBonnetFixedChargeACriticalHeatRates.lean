import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHeatAmplitude

/-!
# Physical reciprocal-gap divergence laws and equal phase amplitudes

Multiplying either actual heat capacity by the temperature or pressure
gap has a positive finite limit. Their ratio tends to one even with
independent entropy references.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeA_small_heat_capacity_temperature_gap_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeASmallRadius w φ τ) * (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) /
        (3 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ)))) := by
  have h := (egbFixedChargeA_small_heat_capacity_amplitude w φ l).mul (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ)
  rw [egbFixedChargeACriticalHeatAmplitude_temperature_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_large_heat_capacity_temperature_gap_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeALargeRadius w φ τ) * (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) /
        (3 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ)))) := by
  have h := (egbFixedChargeA_large_heat_capacity_amplitude w φ l).mul (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ)
  rw [egbFixedChargeACriticalHeatAmplitude_temperature_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_small_heat_capacity_pressure_gap_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeASmallRadius w φ τ) * (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (6 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ)))) := by
  have h := (egbFixedChargeA_small_heat_capacity_amplitude w φ l).mul (egbFixedChargeAPressureGap_quadratic_critical_limit w φ)
  rw [egbFixedChargeACriticalHeatAmplitude_pressure_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_large_heat_capacity_pressure_gap_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeALargeRadius w φ τ) * (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (6 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ)))) := by
  have h := (egbFixedChargeA_large_heat_capacity_amplitude w φ l).mul (egbFixedChargeAPressureGap_quadratic_critical_limit w φ)
  rw [egbFixedChargeACriticalHeatAmplitude_pressure_product] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_heat_capacity_ratio_critical_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₁
      (egbFixedChargeASmallRadius w φ τ) /
        egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂ (egbFixedChargeALargeRadius w φ τ))
      atBot (𝓝 (1 : ℝ)) := by
  have hc := egbFixedChargeACriticalHeatAmplitude_pos w φ
  have h := (egbFixedChargeA_small_heat_capacity_amplitude w φ l₁).div (egbFixedChargeA_large_heat_capacity_amplitude w φ l₂) hc.ne'
  rw [div_self hc.ne'] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
