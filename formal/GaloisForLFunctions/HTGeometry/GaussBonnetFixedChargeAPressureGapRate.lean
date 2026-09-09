import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanPressureRatio

/-!
# Exact critical closing rate of the physical coexistence pressure gap

The fixed-charge pressure gap is quadratic in symmetric radius asymmetry.
Its amplitude is positive at every allowed conserved charge mixture.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPressureGapCoefficient (w φ : ℝ) : ℝ :=
  (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) /
    (12 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeAPressureGapCoefficient_pos (w φ : ℝ) : 0 < egbFixedChargeAPressureGapCoefficient w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  unfold egbFixedChargeAPressureGapCoefficient
  positivity

theorem egbFixedChargeAPressureGapCoefficient_formula (w φ : ℝ) :
    egbFixedChargeACriticalTemperature w φ * egbFixedChargeAPressureRatioGapCoefficient w φ +
      egbFixedChargeATemperatureGapCoefficient w φ * (egbFixedChargeACriticalPressure w φ / egbFixedChargeACriticalTemperature w φ) =
    egbFixedChargeAPressureGapCoefficient w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  rw [egbFixedChargeACritical_pressure_temperature_ratio]
  unfold egbFixedChargeAPressureRatioGapCoefficient
  rw [egbFixedChargeAMeanRadiusCorrection_relative, egbFixedChargeAMeanPressureNumeratorCorrection_relative]
  unfold egbFixedChargeAMeanRelativeCorrection egbFixedChargeATemperatureGapCoefficient egbFixedChargeAPressureGapCoefficient egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeAPressureGap_normalized_formula (w φ τ : ℝ) :
    (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2 =
      egbFixedChargeACriticalTemperature w φ *
        ((egbFixedChargeACriticalPressure w φ / egbFixedChargeACriticalTemperature w φ - egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2) +
      ((egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2) *
        (egbFixedChargeAPressure w φ τ / egbFixedChargeATemperature w φ τ) := by
  have hT := egbFixedChargeATemperature_pos w φ τ
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  have hTc : 0 < egbFixedChargeACriticalTemperature w φ := by unfold egbFixedChargeACriticalTemperature; positivity
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

theorem egbFixedChargeAPressureGap_quadratic_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeAPressureGapCoefficient w φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  have hTc : 0 < egbFixedChargeACriticalTemperature w φ := by unfold egbFixedChargeACriticalTemperature; positivity
  simp only [egbFixedChargeAPressureGap_normalized_formula]
  have hR := (egbFixedChargeAPressure_critical_limit w φ).div (egbFixedChargeATemperature_critical_limit w φ) hTc.ne'
  have h := ((tendsto_const_nhds (x := egbFixedChargeACriticalTemperature w φ)).mul
    (egbFixedChargeAPressureRatioGap_quadratic_critical_limit w φ)).add ((egbFixedChargeATemperatureGap_quadratic_critical_limit w φ).mul hR)
  rwa [egbFixedChargeAPressureGapCoefficient_formula] at h

end GaloisForLFunctions.HTGeometry
