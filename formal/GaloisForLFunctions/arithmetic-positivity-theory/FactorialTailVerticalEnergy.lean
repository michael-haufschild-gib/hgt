import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailReadout

/-! The logarithmic Fourier budget on literal vertical Mellin lines. The change
of variables retains the sign and Jacobian of the corpus Fourier convention. -/

open MeasureTheory Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticPositivityTheory
noncomputable section
set_option autoImplicit false

private def verticalLogScale : ℝ := 1+Real.log (2+2*Real.pi)

private theorem verticalLogScale_pos : 0 < verticalLogScale := by
  have h := Real.log_nonneg (show 1 ≤ 2+2*Real.pi by have := Real.pi_pos; linarith)
  unfold verticalLogScale
  linarith

private theorem vertical_scaled_weight_le (ξ : ℝ) :
    1+Real.log (2+|-(2*Real.pi)*ξ|) ≤ verticalLogScale*suzukiLogWeight ξ := by
  have hp : 0 < 2*Real.pi := by positivity
  have ha : 0 ≤ Real.log (2+2*Real.pi) := Real.log_nonneg (by linarith)
  rw [abs_mul, abs_neg, abs_of_pos hp]
  by_cases hx : |ξ| ≤ 1
  · have hl : Real.log (2+(2*Real.pi)*|ξ|) ≤ Real.log (2+2*Real.pi) :=
      Real.log_le_log (by positivity) (by nlinarith)
    calc
      1+Real.log (2+(2*Real.pi)*|ξ|) ≤ verticalLogScale := by
        unfold verticalLogScale
        linarith only [hl]
      _ ≤ verticalLogScale*suzukiLogWeight ξ :=
        le_mul_of_one_le_right verticalLogScale_pos.le (one_le_suzukiLogWeight ξ)
  · have hx' : 1 < |ξ| := lt_of_not_ge hx
    have hl : Real.log (2+(2*Real.pi)*|ξ|) ≤
        Real.log (2+2*Real.pi)+Real.log |ξ| := by
      rw [← Real.log_mul (by positivity : 2+2*Real.pi ≠ 0) (by positivity : |ξ| ≠ 0)]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hxlog : 0 ≤ Real.log |ξ| := Real.log_nonneg hx'.le
    rw [suzukiLogWeight,max_eq_left hxlog]
    unfold verticalLogScale
    nlinarith [mul_nonneg ha hxlog]

/-- The zero-count weight on an actual vertical Mellin line. -/
def factorialTailVerticalDensity (n : ℕ) (σ t : ℝ) : ℝ :=
  (1+Real.log (2+|t|))*‖factorialTailReadout n ((σ : ℂ)+(t : ℂ)*Complex.I)‖^2

private theorem vertical_density_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ factorialTailVerticalDensity n σ t := by
  unfold factorialTailVerticalDensity
  have hl : 0 ≤ Real.log (2+|t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  positivity

private theorem vertical_density_continuous (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Continuous (factorialTailVerticalDensity n σ) := by
  have hc : Continuous (fun t : ℝ => factorialTailReadout n
      (((σ : ℝ) : ℂ)+(t : ℂ)*Complex.I)) :=
    (factorialTailReadout_analyticOnNhd n).continuousOn.comp_continuous
      (by fun_prop) (fun t => by
        change -1 < ((((σ : ℝ) : ℂ)+(t : ℂ)*Complex.I)).re
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        have := σ.2.1
        linarith)
  have hl : Continuous (fun t : ℝ => Real.log (2+|t|)) := by
    apply Continuous.log (by fun_prop)
    intro t
    positivity
  exact (continuous_const.add hl).mul (hc.norm.pow 2)

private theorem vertical_scaled_density_le (n : ℕ) (σ ξ : ℝ) :
    factorialTailVerticalDensity n σ (-(2*Real.pi)*ξ) ≤
      verticalLogScale*(suzukiLogWeight ξ*‖factorialTailFourier n σ ξ‖^2) := by
  unfold factorialTailVerticalDensity
  rw [factorialTailReadout_add_im_eq_fourier]
  have he : -(-(2*Real.pi)*ξ)/(2*Real.pi) = ξ := by field_simp
  rw [he]
  exact (mul_le_mul_of_nonneg_right (vertical_scaled_weight_le ξ) (sq_nonneg _)).trans_eq
    (by ring)

/-- Integrability is established before changing variables in the vertical budget. -/
theorem factorialTailVertical_integrable (n : ℕ) (σ : FactorialSamplingAbscissa) :
    Integrable (factorialTailVerticalDensity n σ) := by
  have hc := (vertical_density_continuous n σ).comp
    (continuous_const.mul continuous_id : Continuous (fun ξ : ℝ => -(2*Real.pi)*ξ))
  have hi : Integrable (fun ξ : ℝ => factorialTailVerticalDensity n σ (-(2*Real.pi)*ξ)) := by
    apply ((factorialTailLogFourier_integrable n σ).const_mul verticalLogScale).mono'
      hc.aestronglyMeasurable
    filter_upwards [] with ξ
    change ‖factorialTailVerticalDensity n σ (-(2*Real.pi)*ξ)‖ ≤
      verticalLogScale*(suzukiLogWeight ξ*‖factorialTailFourier n σ ξ‖^2)
    rw [Real.norm_eq_abs, abs_of_nonneg (vertical_density_nonneg n σ _)]
    exact vertical_scaled_density_le n σ ξ
  exact (integrable_comp_mul_left_iff _ (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))).mp hi

/-- Uniform vertical-line constant, including the Fourier Jacobian. -/
def factorialTailVerticalConstant : ℝ :=
  (2*Real.pi)*verticalLogScale*factorialTailLogFourierConstant

theorem factorialTailVerticalConstant_pos : 0 < factorialTailVerticalConstant := by
  exact mul_pos (mul_pos (by positivity) verticalLogScale_pos) factorialTailLogFourierConstant_pos

/-- The literal Mellin energy has the same sharp logarithmic scale throughout the enlarged strip. -/
theorem factorialTailVertical_integral_le (n : ℕ) (σ : FactorialSamplingAbscissa) :
    (∫ t : ℝ, factorialTailVerticalDensity n σ t) ≤
      factorialTailVerticalConstant*(1+Real.log (n+1 : ℝ))/(n+1 : ℝ) := by
  have hp : 0 < 2*Real.pi := by positivity
  have hi := factorialTailVertical_integrable n σ
  have his := hi.comp_mul_left' (R := -(2*Real.pi)) (neg_ne_zero.mpr hp.ne')
  have hb := integral_mono his
    ((factorialTailLogFourier_integrable n σ).const_mul verticalLogScale)
    (vertical_scaled_density_le n σ)
  rw [integral_const_mul] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    (factorialTailLogFourier_integral_le n σ) verticalLogScale_pos.le)
  have he := Measure.integral_comp_mul_left (factorialTailVerticalDensity n σ) (-(2*Real.pi))
  simp only [abs_inv,abs_neg,abs_of_pos hp,smul_eq_mul] at he
  have hs : (∫ t : ℝ, factorialTailVerticalDensity n σ t) =
      (2*Real.pi)*(∫ ξ : ℝ, factorialTailVerticalDensity n σ (-(2*Real.pi)*ξ)) := by
    rw [he]
    field_simp
  rw [hs]
  exact (mul_le_mul_of_nonneg_left hb' hp.le).trans_eq (by unfold factorialTailVerticalConstant; push_cast; ring)

end
end GaloisForLFunctions.ArithmeticPositivityTheory
