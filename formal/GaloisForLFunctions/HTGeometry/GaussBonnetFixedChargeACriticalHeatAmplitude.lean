import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSlopeProfile

/-!
# Equal leading heat-capacity amplitudes for the two actual phases

Both heat capacities grow like the reciprocal squared radius asymmetry.
The amplitude is explicit, strictly positive and independent of the
entropy reference. Its products with the physical gap amplitudes are
finite and nonzero.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalHeatAmplitude (w φ : ℝ) : ℝ :=
  2 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
    (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)

theorem egbFixedChargeACriticalHeatAmplitude_pos (w φ : ℝ) : 0 < egbFixedChargeACriticalHeatAmplitude w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalHeatAmplitude
  positivity

theorem egbFixedChargeACriticalHeatAmplitude_formula (w φ : ℝ) :
    egbFixedChargeACriticalHeatNumerator w φ / egbFixedChargeACriticalSlopeCoefficient w φ =
      egbFixedChargeACriticalHeatAmplitude w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  rw [egbFixedChargeACritical_heat_numerator_value]
  unfold egbFixedChargeACriticalHeatAmplitude egbFixedChargeACriticalSlopeCoefficient
  field_simp <;> ring

theorem egbFixedChargeA_small_heat_capacity_amplitude (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeASmallRadius w φ τ) * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeACriticalHeatAmplitude w φ)) := by
  have h := (egbFixedChargeA_small_heat_numerator_critical_limit w φ).div
    (egbFixedChargeA_small_radial_slope_quadratic_limit w φ) (egbFixedChargeACriticalSlopeCoefficient_pos w φ).ne'
  rw [egbFixedChargeACriticalHeatAmplitude_formula] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_small_heat_capacity_formula]
  field_simp <;> ring

theorem egbFixedChargeA_large_heat_capacity_amplitude (w φ l : ℝ) :
    Tendsto (fun τ => egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
      (egbFixedChargeALargeRadius w φ τ) * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeACriticalHeatAmplitude w φ)) := by
  have h := (egbFixedChargeA_large_heat_numerator_critical_limit w φ).div
    (egbFixedChargeA_large_radial_slope_quadratic_limit w φ) (egbFixedChargeACriticalSlopeCoefficient_pos w φ).ne'
  rw [egbFixedChargeACriticalHeatAmplitude_formula] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_large_heat_capacity_formula]
  field_simp <;> ring

theorem egbFixedChargeACriticalHeatAmplitude_temperature_product (w φ : ℝ) :
    egbFixedChargeACriticalHeatAmplitude w φ * egbFixedChargeATemperatureGapCoefficient w φ =
      egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) /
        (3 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalHeatAmplitude egbFixedChargeATemperatureGapCoefficient egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeACriticalHeatAmplitude_pressure_product (w φ : ℝ) :
    egbFixedChargeACriticalHeatAmplitude w φ * egbFixedChargeAPressureGapCoefficient w φ =
      (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (6 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalHeatAmplitude egbFixedChargeAPressureGapCoefficient
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
