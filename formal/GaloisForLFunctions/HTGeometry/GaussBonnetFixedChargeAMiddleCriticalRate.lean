import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleMeanLimits

/-!
# Exact quadratic displacement of the unstable equilibrium

The middle root lies below the arithmetic mean at second order. Its
first-order displacement vanishes, so it approaches the center of the
rescaled phase interval. The coefficient follows from an exact quadratic
residual, not an assumed root expansion.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMiddleMeanCorrection (φ : ℝ) : ℝ :=
  -(5 - 14 * egbFixedChargeACriticalCouplingWeight φ) /
    (20 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeAMiddleMeanCorrection_neg (φ : ℝ) : egbFixedChargeAMiddleMeanCorrection φ < 0 := by
  have hb := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have h5 : 0 < 5 - 14 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMiddleMeanCorrection
  exact div_neg_of_neg_of_pos (neg_neg_of_pos h5) (by positivity)

theorem egbFixedChargeAMiddleMeanRatio_normalized_difference (τ φ : ℝ) :
    (egbFixedChargeAMiddleMeanRatio τ φ - 1) / egbCoexistenceASymmetricRatio τ ^ 2 =
      -((egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
        egbCoexistenceASymmetricRatio τ ^ 2) /
      (egbFixedChargeAMeanPressureNumerator τ φ * (egbFixedChargeAMiddleMeanRatio τ φ + 1) + egbFixedChargeAMiddleMeanLinear τ φ) := by
  apply (eq_div_iff (egbFixedChargeAMiddleMeanSecant_pos τ φ).ne').2
  calc
    _ = ((egbFixedChargeAMiddleMeanRatio τ φ - 1) *
      (egbFixedChargeAMeanPressureNumerator τ φ * (egbFixedChargeAMiddleMeanRatio τ φ + 1) + egbFixedChargeAMiddleMeanLinear τ φ)) /
        egbCoexistenceASymmetricRatio τ ^ 2 := by ring
    _ = _ := by rw [egbFixedChargeAMiddleMeanRatio_difference_cross]; ring

theorem egbFixedChargeAMiddleMeanRatio_quadratic_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleMeanRatio τ φ - 1) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeAMiddleMeanCorrection φ)) := by
  have hb := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have h := (egbFixedChargeAMiddleMeanResidual_critical_limit φ).neg.div (egbFixedChargeAMiddleMeanSecant_critical_limit φ) (by positivity)
  have he : -(1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) /
      (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) = egbFixedChargeAMiddleMeanCorrection φ := by
    unfold egbFixedChargeAMiddleMeanCorrection
    field_simp <;> ring
  rw [he] at h
  simp only [egbFixedChargeAMiddleMeanRatio_normalized_difference]
  simpa only [Pi.div_def] using h

theorem egbFixedChargeAMiddleMeanRatio_linear_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleMeanRatio τ φ - 1) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMiddleMeanRatio_quadratic_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMiddleRadius_mean_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ)) := by
  have h := (egbFixedChargeAMeanRadius_critical_limit w φ).mul (egbFixedChargeAMiddleMeanRatio_quadratic_limit φ)
  convert h using 1
  funext τ
  rw [egbFixedChargeAMiddleRadius_mean_formula]
  ring

theorem egbFixedChargeAMiddleRadius_mean_linear_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanRadius_critical_limit w φ).mul (egbFixedChargeAMiddleMeanRatio_linear_limit φ)
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  rw [egbFixedChargeAMiddleRadius_mean_formula]
  ring

theorem egbFixedChargeAMiddleRadius_critical_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeAMeanRadiusCorrection w φ + egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ)) := by
  have h := (egbFixedChargeAMeanRadius_quadratic_critical_limit w φ).add (egbFixedChargeAMiddleRadius_mean_quadratic_limit w φ)
  convert h using 1
  funext τ
  ring

theorem egbFixedChargeAMiddleRadius_critical_linear_limit (w φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeACriticalRadius w φ) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMiddleRadius_critical_quadratic_limit w φ).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMiddleRadius_eventually_below_mean (w φ : ℝ) :
    ∀ᶠ τ in atBot, egbFixedChargeAMiddleRadius w φ τ < egbFixedChargeAMeanRadius w φ τ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have hneg : egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ < 0 := mul_neg_of_pos_of_neg hr hc
  have h := (egbFixedChargeAMiddleRadius_mean_quadratic_limit w φ).eventually_lt_const hneg
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd2 : 0 < egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  have hcross := (div_lt_iff₀ hd2).1 hτ
  linarith

end GaloisForLFunctions.HTGeometry
