import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorThermodynamics
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHeatRates

/-!
# Negative heat-capacity amplitude at the arithmetic mean radius

The actual mean-radius state is not either equilibrium phase. Its
heat-capacity amplitude is minus twice the common phase amplitude,
quantifying the unstable state between the two stable phases.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeA_mean_heat_capacity_amplitude (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeAMeanRadius w φ τ) * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (-2 * egbFixedChargeACriticalHeatAmplitude w φ)) := by
  have hc := egbFixedChargeACriticalSlopeCoefficient_pos w φ
  have hnum := egbFixedChargeAInterior_heat_numerator_critical_limit w φ 0
  simp only [egbFixedChargeAInteriorRadius_mean] at hnum
  have h := hnum.div (egbFixedChargeA_mean_radial_slope_quadratic_limit w φ) (by linarith)
  have he : (2 / 3 : ℝ) / (-egbFixedChargeACriticalSlopeCoefficient w φ / 2) =
      -2 * egbFixedChargeACriticalHeatAmplitude w φ := by
    rw [← egbFixedChargeACriticalHeatAmplitude_formula, egbFixedChargeACritical_heat_numerator_value]
    field_simp <;> ring
  rw [he] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hf := egbFixedChargeAInterior_heat_capacity_formula w φ τ 0 l
  simp only [egbFixedChargeAInteriorRadius_mean] at hf
  rw [hf]
  field_simp <;> ring

theorem egbFixedChargeA_mean_large_heat_capacity_ratio (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₁
      (egbFixedChargeAMeanRadius w φ τ) /
        egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l₂ (egbFixedChargeALargeRadius w φ τ))
      atBot (𝓝 (-2 : ℝ)) := by
  have hc := egbFixedChargeACriticalHeatAmplitude_pos w φ
  have h := (egbFixedChargeA_mean_heat_capacity_amplitude w φ l₁).div (egbFixedChargeA_large_heat_capacity_amplitude w φ l₂) hc.ne'
  have he : -2 * egbFixedChargeACriticalHeatAmplitude w φ / egbFixedChargeACriticalHeatAmplitude w φ = -2 := by field_simp
  rw [he] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_mean_heat_capacity_temperature_gap_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeAMeanRadius w φ τ) * (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (-2 * (egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) /
        (3 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))))) := by
  have h := (egbFixedChargeA_mean_heat_capacity_amplitude w φ l).mul (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ)
  have he : (-2 * egbFixedChargeACriticalHeatAmplitude w φ) * egbFixedChargeATemperatureGapCoefficient w φ =
      -2 * (egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) /
        (3 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))) := by
    rw [mul_assoc, egbFixedChargeACriticalHeatAmplitude_temperature_product]
  rw [he] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_mean_heat_capacity_pressure_gap_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeAMeanRadius w φ τ) * (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 (-2 * ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (6 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))))) := by
  have h := (egbFixedChargeA_mean_heat_capacity_amplitude w φ l).mul (egbFixedChargeAPressureGap_quadratic_critical_limit w φ)
  have he : (-2 * egbFixedChargeACriticalHeatAmplitude w φ) * egbFixedChargeAPressureGapCoefficient w φ =
      -2 * ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (6 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))) := by
    rw [mul_assoc, egbFixedChargeACriticalHeatAmplitude_pressure_product]
  rw [he] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeA_mean_heat_capacity_eventually_neg (w φ l : ℝ) :
    ∀ᶠ τ in atBot, egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeAMeanRadius w φ τ) < 0 := by
  have hc := egbFixedChargeACriticalHeatAmplitude_pos w φ
  have h := (egbFixedChargeA_mean_heat_capacity_amplitude w φ l).eventually_lt_const (show -2 * egbFixedChargeACriticalHeatAmplitude w φ < 0 by linarith)
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd2 : 0 < egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  nlinarith

end GaloisForLFunctions.HTGeometry
