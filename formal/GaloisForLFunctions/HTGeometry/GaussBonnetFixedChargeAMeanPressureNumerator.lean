import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanThermalCorrection

/-!
# Critical expansion of the physical pressure-to-temperature numerator
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanPressureNumerator (τ φ : ℝ) : ℝ :=
  3 * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) + 2 * egbFixedChargeAMeanCoupling τ φ * (2 - egbCoexistenceALogKernel τ)
def egbFixedChargeAMeanPressureNumeratorCorrection (φ : ℝ) : ℝ :=
  3 - 2 * egbFixedChargeAFraction φ * egbFixedChargeAMeanCriticalCorrection φ - 16 * egbFixedChargeACriticalCouplingWeight φ / 5

theorem egbFixedChargeAMeanPressureNumerator_normalized_difference (τ φ : ℝ) :
    (egbFixedChargeAMeanPressureNumerator τ φ - (3 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
      3 + 2 * (((egbFixedChargeAMeanCoupling τ φ - egbFixedChargeACriticalCouplingWeight φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * (2 - egbCoexistenceALogKernel τ) -
        egbFixedChargeACriticalCouplingWeight φ * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanPressureNumerator
  field_simp <;> ring

theorem egbFixedChargeAMeanPressureNumerator_quadratic_critical_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanPressureNumerator τ φ - (3 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanPressureNumeratorCorrection φ)) := by
  simp only [egbFixedChargeAMeanPressureNumerator_normalized_difference]
  have h1 := (egbFixedChargeAMeanCoupling_quadratic_critical_limit φ).mul
    ((tendsto_const_nhds (x := (2 : ℝ))).sub egbCoexistenceALogKernel_tendsto_critical)
  have h2 := (tendsto_const_nhds (x := egbFixedChargeACriticalCouplingWeight φ)).mul egbCoexistenceALogKernel_asymmetry_quadratic_limit
  have h := (tendsto_const_nhds (x := (3 : ℝ))).add ((tendsto_const_nhds (x := (2 : ℝ))).mul (h1.sub h2))
  convert h using 1
  unfold egbFixedChargeAMeanPressureNumeratorCorrection
  ring

theorem egbFixedChargeAMeanPressureNumeratorCorrection_relative (φ : ℝ) :
    egbFixedChargeAMeanPressureNumeratorCorrection φ = 3 + 2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeAMeanRelativeCorrection φ -
      16 * egbFixedChargeACriticalCouplingWeight φ / 5 := by
  unfold egbFixedChargeAMeanPressureNumeratorCorrection
  rw [egbFixedChargeAMeanCriticalCorrection_relative]
  unfold egbFixedChargeACriticalCouplingWeight
  ring

theorem egbFixedChargeACritical_pressure_temperature_ratio (w φ : ℝ) :
    egbFixedChargeACriticalPressure w φ / egbFixedChargeACriticalTemperature w φ =
      (3 - 2 * egbFixedChargeACriticalCouplingWeight φ) / (16 * egbFixedChargeACriticalRadius w φ) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalPressure egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeA_mean_pressure_radius_product_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAMeanRadiusCorrection w φ + egbFixedChargeACriticalRadius w φ)) := by
  have h := (egbFixedChargeAMeanRadius_quadratic_critical_limit w φ).add (egbFixedChargeAMeanRadius_critical_limit w φ)
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
