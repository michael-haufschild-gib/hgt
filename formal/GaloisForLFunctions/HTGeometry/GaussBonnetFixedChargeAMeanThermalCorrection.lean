import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanRelativeCorrection
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanThermodynamics

/-!
# Quadratic closing rate of the physical coexistence temperature gap

The logarithmic moment coefficient determines the first mean-denominator
correction. Combining it with the conserved-charge mean-radius correction
gives an exact positive amplitude for T_c - T along the actual branch.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanThermalCorrection (φ : ℝ) : ℝ :=
  -2 + 12 * egbFixedChargeAFraction φ * egbFixedChargeAMeanCriticalCorrection φ +
    32 * egbFixedChargeACriticalCouplingWeight φ / 5

def egbFixedChargeATemperatureGapCoefficient (w φ : ℝ) : ℝ :=
  egbFixedChargeACriticalTemperature w φ * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) /
    (2 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeAMeanDenominator_normalized_difference (τ φ : ℝ) :
    (egbFixedChargeAMeanDenominator τ φ - (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      -2 + 4 * (((egbFixedChargeAMeanCoupling τ φ - egbFixedChargeACriticalCouplingWeight φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * egbCoexistenceALogKernel τ +
        egbFixedChargeACriticalCouplingWeight φ * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanDenominator
  field_simp <;> ring

theorem egbFixedChargeAMeanDenominator_quadratic_critical_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanDenominator τ φ - (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanThermalCorrection φ)) := by
  simp only [egbFixedChargeAMeanDenominator_normalized_difference]
  have h1 := (egbFixedChargeAMeanCoupling_quadratic_critical_limit φ).mul egbCoexistenceALogKernel_tendsto_critical
  have h2 := (tendsto_const_nhds (x := egbFixedChargeACriticalCouplingWeight φ)).mul egbCoexistenceALogKernel_asymmetry_quadratic_limit
  have h := (tendsto_const_nhds (x := (-2 : ℝ))).add ((tendsto_const_nhds (x := (4 : ℝ))).mul (h1.add h2))
  convert h using 1
  unfold egbFixedChargeAMeanThermalCorrection
  ring

theorem egbFixedChargeAMeanThermalCorrection_relative (φ : ℝ) :
    egbFixedChargeAMeanThermalCorrection φ = -2 - 12 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeAMeanRelativeCorrection φ +
      32 * egbFixedChargeACriticalCouplingWeight φ / 5 := by
  unfold egbFixedChargeAMeanThermalCorrection
  rw [egbFixedChargeAMeanCriticalCorrection_relative]
  unfold egbFixedChargeACriticalCouplingWeight
  ring

theorem egbFixedChargeACritical_temperature_mean (w φ : ℝ) :
    egbFixedChargeACriticalTemperature w φ =
      2 / (Real.pi * egbFixedChargeACriticalRadius w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeATemperatureGapCoefficient_formula (w φ : ℝ) :
    2 * (egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanThermalCorrection φ +
      egbFixedChargeAMeanRadiusCorrection w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) /
      (Real.pi * (egbFixedChargeACriticalRadius w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) ^ (2 : ℕ)) =
    egbFixedChargeATemperatureGapCoefficient w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  rw [egbFixedChargeAMeanThermalCorrection_relative, egbFixedChargeAMeanRadiusCorrection_relative]
  unfold egbFixedChargeAMeanRelativeCorrection egbFixedChargeATemperatureGapCoefficient egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeATemperatureGapCoefficient_pos (w φ : ℝ) : 0 < egbFixedChargeATemperatureGapCoefficient w φ := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hpi := Real.pi_pos
  unfold egbFixedChargeATemperatureGapCoefficient egbFixedChargeACriticalTemperature
  positivity

theorem egbFixedChargeA_mean_thermal_product_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAMeanDenominator τ φ -
      egbFixedChargeACriticalRadius w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanThermalCorrection φ +
        egbFixedChargeAMeanRadiusCorrection w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have h := ((egbFixedChargeAMeanRadius_critical_limit w φ).mul (egbFixedChargeAMeanDenominator_quadratic_critical_limit φ)).add
    ((egbFixedChargeAMeanRadius_quadratic_critical_limit w φ).mul (tendsto_const_nhds (x := 6 + 12 * egbFixedChargeACriticalCouplingWeight φ)))
  convert h using 1
  funext τ
  ring

theorem egbFixedChargeATemperatureGap_normalized_formula (w φ τ : ℝ) :
    (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      2 * ((egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAMeanDenominator τ φ -
        egbFixedChargeACriticalRadius w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) /
      (Real.pi * (egbFixedChargeACriticalRadius w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)) *
        (egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAMeanDenominator τ φ)) := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hpi := Real.pi_pos
  rw [egbFixedChargeACritical_temperature_mean, egbFixedChargeA_mean_temperature]
  field_simp <;> ring

theorem egbFixedChargeATemperatureGap_quadratic_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeATemperatureGapCoefficient w φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  simp only [egbFixedChargeATemperatureGap_normalized_formula]
  have hn := (tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeA_mean_thermal_product_limit w φ)
  have hd := (tendsto_const_nhds (x := Real.pi * (egbFixedChargeACriticalRadius w φ * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ)))).mul
    ((egbFixedChargeAMeanRadius_critical_limit w φ).mul (egbFixedChargeAMeanDenominator_critical_limit φ))
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  rw [← egbFixedChargeATemperatureGapCoefficient_formula]
  congr 1
  ring

end GaloisForLFunctions.HTGeometry
