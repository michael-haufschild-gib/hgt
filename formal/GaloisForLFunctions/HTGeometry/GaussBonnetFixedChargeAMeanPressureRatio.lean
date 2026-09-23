import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanPressureNumerator

/-!
# Critical quadratic correction of the actual pressure-temperature ratio
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPressureRatioGapCoefficient (w φ : ℝ) : ℝ :=
  ((3 - 2 * egbFixedChargeACriticalCouplingWeight φ) * (egbFixedChargeAMeanRadiusCorrection w φ + egbFixedChargeACriticalRadius w φ) -
    egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanPressureNumeratorCorrection φ) /
      (16 * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ))

theorem egbFixedChargeAPressureRatioGap_normalized_formula (w φ τ : ℝ) :
    (egbFixedChargeACriticalPressure w φ / egbFixedChargeACriticalTemperature w φ - egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) =
    ((3 - 2 * egbFixedChargeACriticalCouplingWeight φ) * ((egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) -
      egbFixedChargeACriticalRadius w φ * ((egbFixedChargeAMeanPressureNumerator τ φ - (3 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) /
      (16 * egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  rw [egbFixedChargeACritical_pressure_temperature_ratio, egbFixedChargeA_mean_pressure_temperature_ratio]
  unfold egbFixedChargeAMeanPressureNumerator
  field_simp <;> ring

theorem egbFixedChargeAPressureRatioGap_quadratic_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeACriticalPressure w φ / egbFixedChargeACriticalTemperature w φ -
      egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (egbFixedChargeAPressureRatioGapCoefficient w φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  simp only [egbFixedChargeAPressureRatioGap_normalized_formula]
  have hn := ((tendsto_const_nhds (x := 3 - 2 * egbFixedChargeACriticalCouplingWeight φ)).mul
    (egbFixedChargeA_mean_pressure_radius_product_limit w φ)).sub
      ((tendsto_const_nhds (x := egbFixedChargeACriticalRadius w φ)).mul (egbFixedChargeAMeanPressureNumerator_quadratic_critical_limit φ))
  have hx : Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  have hd := ((tendsto_const_nhds (x := 16 * egbFixedChargeACriticalRadius w φ)).mul (egbFixedChargeAMeanRadius_critical_limit w φ)).mul hx
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  unfold egbFixedChargeAPressureRatioGapCoefficient
  congr 1
  ring

end GaloisForLFunctions.HTGeometry
