import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierCriticalLimit
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPressureGapRate

/-!
# Physical critical exponents of the coexistence Gibbs barrier

The quartic asymmetry law becomes quadratic in either temperature or
pressure distance to criticality, and quartic in phase-radius separation.
All limits concern the actual logarithmic-entropy Gibbs free energy.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsBarrier_temperature_amplitude (w φ : ℝ) :
    egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeATemperatureGapCoefficient w φ ^ (2 : ℕ) =
      3 * Real.pi ^ (2 : ℕ) * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ) *
        (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hp := Real.pi_pos
  unfold egbFixedChargeAGibbsBarrierCoefficient egbFixedChargeATemperatureGapCoefficient egbFixedChargeACriticalTemperature
  field_simp <;> ring

theorem egbFixedChargeAGibbsBarrier_pressure_amplitude (w φ : ℝ) :
    egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeAPressureGapCoefficient w φ ^ (2 : ℕ) =
      12 * Real.pi ^ (2 : ℕ) * egbFixedChargeACriticalRadius w φ ^ (5 : ℕ) *
        (1 + 6 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hp := Real.pi_pos
  unfold egbFixedChargeAGibbsBarrierCoefficient egbFixedChargeAPressureGapCoefficient
  field_simp <;> ring

theorem egbFixedChargeAGibbsBarrier_temperature_quadratic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l /
      (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ) ^ (2 : ℕ))
      atBot (𝓝 (3 * Real.pi ^ (2 : ℕ) * egbFixedChargeACriticalRadius w φ ^ (3 : ℕ) *
        (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have hT := egbFixedChargeATemperatureGapCoefficient_pos w φ
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).div
    ((egbFixedChargeATemperatureGap_quadratic_critical_limit w φ).pow 2) (by positivity)
  simp only [Pi.div_def] at h
  rw [egbFixedChargeAGibbsBarrier_temperature_amplitude] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hgap := sub_pos.mpr (egbFixedChargeATemperature_below_critical w φ τ)
  field_simp

theorem egbFixedChargeAGibbsBarrier_pressure_quadratic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l /
      (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) ^ (2 : ℕ))
      atBot (𝓝 (12 * Real.pi ^ (2 : ℕ) * egbFixedChargeACriticalRadius w φ ^ (5 : ℕ) *
        (1 + 6 * egbFixedChargeACriticalCouplingWeight φ) ^ (2 : ℕ) /
        ((1 + 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)))) := by
  have hP := egbFixedChargeAPressureGapCoefficient_pos w φ
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).div
    ((egbFixedChargeAPressureGap_quadratic_critical_limit w φ).pow 2) (by positivity)
  simp only [Pi.div_def] at h
  rw [egbFixedChargeAGibbsBarrier_pressure_amplitude] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hgap := sub_pos.mpr (egbFixedChargeAPressure_below_critical w φ τ)
  field_simp

theorem egbFixedChargeAGibbsBarrier_radius_quartic_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l /
      (egbFixedChargeALargeRadius w φ τ - egbFixedChargeASmallRadius w φ τ) ^ (4 : ℕ))
      atBot (𝓝 (egbFixedChargeACriticalQuarticCoefficient w φ / 16)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).div
    ((egbFixedChargeA_radius_gap_asymmetry_limit w φ).pow 4) (by positivity)
  simp only [Pi.div_def] at h
  have he : egbFixedChargeAGibbsBarrierCoefficient w φ / (2 * egbFixedChargeACriticalRadius w φ) ^ (4 : ℕ) =
      egbFixedChargeACriticalQuarticCoefficient w φ / 16 := by
    rw [egbFixedChargeAGibbsBarrierCoefficient_critical_quartic]
    field_simp
    ring
  rw [he] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

end GaloisForLFunctions.HTGeometry
