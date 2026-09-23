import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleCriticalRate
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPressureGapRate

/-!
# Side and physical rate of approach of the intermediate equilibrium

Although the intermediate radius lies below the phase mean near
criticality, it lies above the critical radius. Its displacement is
linear in the temperature or pressure gap, unlike the square-root phase
separation.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMiddleRadiusCorrection (w φ : ℝ) : ℝ :=
  egbFixedChargeACriticalRadius w φ *
    (35 + 8 * egbFixedChargeACriticalCouplingWeight φ - 252 * egbFixedChargeACriticalCouplingWeight φ ^ (2 : ℕ)) /
    (60 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeAMiddleRadiusCorrection_pos (w φ : ℝ) : 0 < egbFixedChargeAMiddleRadiusCorrection w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hn : 0 < 35 + 8 * egbFixedChargeACriticalCouplingWeight φ - 252 * egbFixedChargeACriticalCouplingWeight φ ^ (2 : ℕ) := by
    nlinarith [mul_nonneg hb (show 0 ≤ 1 / 6 - egbFixedChargeACriticalCouplingWeight φ by linarith)]
  unfold egbFixedChargeAMiddleRadiusCorrection
  positivity

theorem egbFixedChargeAMiddleRadiusCorrection_formula (w φ : ℝ) :
    egbFixedChargeAMeanRadiusCorrection w φ + egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ =
      egbFixedChargeAMiddleRadiusCorrection w φ := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  rw [egbFixedChargeAMeanRadiusCorrection_relative]
  unfold egbFixedChargeAMeanRelativeCorrection egbFixedChargeAMiddleMeanCorrection egbFixedChargeAMiddleRadiusCorrection
  field_simp <;> ring

theorem egbFixedChargeAMiddleRadius_amplitude_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeACriticalRadius w φ) /
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (egbFixedChargeAMiddleRadiusCorrection w φ)) := by
  have h := egbFixedChargeAMiddleRadius_critical_quadratic_limit w φ
  rwa [egbFixedChargeAMiddleRadiusCorrection_formula] at h

theorem egbFixedChargeAMiddleRadius_eventually_above_critical (w φ : ℝ) :
    ∀ᶠ τ in atBot, egbFixedChargeACriticalRadius w φ < egbFixedChargeAMiddleRadius w φ τ := by
  have h := (egbFixedChargeAMiddleRadius_amplitude_limit w φ).eventually_const_lt
    (egbFixedChargeAMiddleRadiusCorrection_pos w φ)
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd2 : 0 < egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  have hcross := (lt_div_iff₀ hd2).1 hτ
  linarith

theorem egbFixedChargeAMiddleRadius_temperature_linear_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeACriticalRadius w φ) /
      (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 (egbFixedChargeAMiddleRadiusCorrection w φ / egbFixedChargeATemperatureGapCoefficient w φ)) := by
  have h := (egbFixedChargeAMiddleRadius_amplitude_limit w φ).div
    (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ) (egbFixedChargeATemperatureGapCoefficient_pos w φ).ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMiddleRadius_pressure_linear_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeACriticalRadius w φ) /
      (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 (egbFixedChargeAMiddleRadiusCorrection w φ / egbFixedChargeAPressureGapCoefficient w φ)) := by
  have h := (egbFixedChargeAMiddleRadius_amplitude_limit w φ).div
    (egbFixedChargeAPressureGap_quadratic_critical_limit w φ) (egbFixedChargeAPressureGapCoefficient_pos w φ).ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

end GaloisForLFunctions.HTGeometry
