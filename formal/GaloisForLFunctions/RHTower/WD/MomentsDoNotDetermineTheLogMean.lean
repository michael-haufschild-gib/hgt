import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The moments of a log-normal law do not determine its log-mean

At a fixed mollifier length the law of `Y = log|ζM(½ + b/log T + it)|` has positive variance and is
log-normal in the Selberg limit. Block 3 of route WD needs its mean `E Y` to precision `o(1)`.
This module shows that no moment data can supply it: two laws of `Y` with the same exponential
moments `E e^{kY}` for every integer `k` (all moments `E X^k`, `k ∈ ℤ`, of `X = e^Y`) have different
means `E Y`.

The laws are Heyde's: `φ(y)` and `φ(y)(1 + sin 2πy)` with `φ` the standard normal density.

* `integral_exp_mul_sin_gaussWeight`: `∫ e^{ky} sin(2πy) e^{−y²/2} dy = 0` for `k ∈ ℤ`, the imaginary
  part of the Gaussian integral `√(2π) e^{(k+2πi)²/2}`, which is real because `e^{2πik} = 1`.
* `integral_mul_sin_gaussWeight`: `∫ y sin(2πy) e^{−y²/2} dy = 2π √(2π) e^{−2π²}`, by parts.
* `logNormal_moments_do_not_determine_logMean`: the two normalized laws share every integer
  exponential moment, and their means differ by `2π e^{−2π²}`.
-/

open Complex Real MeasureTheory

namespace GaloisForLFunctions.RHTower.WD

noncomputable section

/-- The Gaussian weight `e^{−y²/2}`. -/
def gaussWeight (y : ℝ) : ℝ := Real.exp (-(y ^ 2) / 2)

theorem gaussWeight_pos (y : ℝ) : 0 < gaussWeight y := Real.exp_pos _

@[fun_prop]
theorem continuous_gaussWeight : Continuous gaussWeight := by
  unfold gaussWeight; fun_prop

/-- The complex Gaussian integral `∫ e^{−y²/2 + cy} dy = √(2π) e^{c²/2}`. -/
theorem integral_cexp_gauss (c : ℂ) :
    ∫ y : ℝ, cexp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2 + c * y) =
      ((Real.sqrt (2 * π) : ℝ) : ℂ) * cexp (c ^ 2 / 2) := by
  have hb : (-(1 / 2 : ℂ)).re < 0 := by norm_num
  have h := integral_cexp_quadratic hb c 0
  simp only [add_zero] at h
  rw [h]
  congr 1
  · have h2 : (π : ℂ) / -(-(1 / 2 : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  · congr 1; ring

theorem integrable_cexp_gauss (c : ℂ) :
    Integrable (fun y : ℝ => cexp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2 + c * y)) := by
  have h := integrable_cexp_quadratic (b := (1 / 2 : ℂ)) (by norm_num) c 0
  simpa only [add_zero, neg_mul] using h

theorem cexp_gauss_real_mul_I (k a y : ℝ) :
    cexp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2 + ((k : ℂ) + a * I) * y) =
      ((Real.exp (k * y) * gaussWeight y : ℝ) : ℂ) * cexp ((a * y : ℝ) * I) := by
  have h : ((Real.exp (k * y) * gaussWeight y : ℝ) : ℂ) = cexp (((k * y - y ^ 2 / 2 : ℝ) : ℂ)) := by
    unfold gaussWeight
    rw [← Real.exp_add, Complex.ofReal_exp]
    congr 2
    ring
  rw [h, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The odd part has zero integer moments.** -/
theorem integral_exp_mul_sin_gaussWeight (k : ℤ) :
    ∫ y : ℝ, Real.exp (k * y) * Real.sin (2 * π * y) * gaussWeight y = 0 := by
  have hint := integrable_cexp_gauss (((k : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * I)
  have him := integral_im hint
  simp only [RCLike.im_to_complex] at him
  have hpt : ∀ y : ℝ,
      (cexp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2 + (((k : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * I) * y)).im =
      Real.exp (k * y) * Real.sin (2 * π * y) * gaussWeight y := by
    intro y
    rw [cexp_gauss_real_mul_I, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    ring
  simp_rw [hpt] at him
  rw [him, integral_cexp_gauss]
  have hsq : (((k : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * I) ^ 2 / 2 =
      (((k : ℝ) ^ 2 / 2 - 2 * π ^ 2 : ℝ) : ℂ) + ((k : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    linear_combination (2 * (π : ℂ) ^ 2) * Complex.I_sq
  rw [hsq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.ofReal_im]

/-- **By parts:** `∫ y sin(2πy) e^{−y²/2} dy = 2π ∫ cos(2πy) e^{−y²/2} dy = 2π √(2π) e^{−2π²}`. -/
theorem integral_mul_sin_gaussWeight :
    ∫ y : ℝ, y * Real.sin (2 * π * y) * gaussWeight y =
      2 * π * (Real.sqrt (2 * π) * Real.exp (-(2 * π ^ 2))) := by
  -- `u = −e^{−y²/2}`, `u' = y e^{−y²/2}`, `v = sin 2πy`, `v' = 2π cos 2πy`.
  have hint_g : Integrable gaussWeight := by
    have := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    unfold gaussWeight; ring_nf
  have hint_yg : Integrable (fun y : ℝ => y * gaussWeight y) := by
    have := integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    unfold gaussWeight; ring_nf
  have hu : ∀ y : ℝ, HasDerivAt (fun y => -gaussWeight y) (y * gaussWeight y) y := by
    intro y
    have h := ((hasDerivAt_pow 2 y).neg.div_const 2).exp.neg
    refine h.congr_deriv ?_
    unfold gaussWeight
    simp only [Pi.neg_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring_nf
  have hv : ∀ y : ℝ, HasDerivAt (fun y => Real.sin (2 * π * y)) (2 * π * Real.cos (2 * π * y)) y := by
    intro y
    have h := ((hasDerivAt_id' y).const_mul (2 * π)).sin
    convert h using 1
    ring
  have huv' : Integrable (fun y => -gaussWeight y * (2 * π * Real.cos (2 * π * y))) := by
    refine (hint_g.const_mul (2 * π)).mono' ?_ ?_
    · exact (hint_g.aestronglyMeasurable.neg.mul (by fun_prop : Continuous fun y : ℝ =>
        2 * π * Real.cos (2 * π * y)).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall fun y => ?_
      have hg := (gaussWeight_pos y).le
      rw [norm_mul, norm_neg, Real.norm_of_nonneg hg, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have hc := Real.abs_cos_le_one (2 * π * y)
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hg) (sub_nonneg.mpr hc)]
  have hu'v : Integrable (fun y => y * gaussWeight y * Real.sin (2 * π * y)) := by
    refine hint_yg.norm.mono' ?_ ?_
    · exact hint_yg.aestronglyMeasurable.mul (by fun_prop : Continuous fun y : ℝ =>
        Real.sin (2 * π * y)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul, Real.norm_eq_abs (Real.sin _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
  have huv : Integrable (fun y => -gaussWeight y * Real.sin (2 * π * y)) := by
    refine hint_g.mono' ?_ ?_
    · exact hint_g.aestronglyMeasurable.neg.mul (by fun_prop : Continuous fun y : ℝ =>
        Real.sin (2 * π * y)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul, Real.norm_eq_abs (Real.sin _), norm_neg,
        Real.norm_of_nonneg (gaussWeight_pos y).le]
      exact mul_le_of_le_one_right (gaussWeight_pos y).le (Real.abs_sin_le_one _)
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun y _ => hu y) (fun y _ => hv y)
    huv' hu'v huv
  -- `∫ cos(2πy) e^{−y²/2} = Re ∫ e^{−y²/2 + 2πi y}`.
  have hcos : ∫ y : ℝ, gaussWeight y * Real.cos (2 * π * y) =
      Real.sqrt (2 * π) * Real.exp (-(2 * π ^ 2)) := by
    have hint := integrable_cexp_gauss (((0 : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * I)
    have hre := integral_re hint
    simp only [RCLike.re_to_complex] at hre
    have hpt : ∀ y : ℝ,
        (cexp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2 + (((0 : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * I) * y)).re =
        gaussWeight y * Real.cos (2 * π * y) := by
      intro y
      rw [cexp_gauss_real_mul_I, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      simp only [zero_mul, Real.exp_zero, one_mul]
    simp_rw [hpt] at hre
    rw [hre, integral_cexp_gauss]
    have hsq : (((0 : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) * I) ^ 2 / 2 = ((-(2 * π ^ 2) : ℝ) : ℂ) := by
      push_cast
      linear_combination (2 * (π : ℂ) ^ 2) * Complex.I_sq
    rw [hsq, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hl : ∫ y : ℝ, -gaussWeight y * (2 * π * Real.cos (2 * π * y)) =
      -(2 * π * ∫ y : ℝ, gaussWeight y * Real.cos (2 * π * y)) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; ext y; ring
  have hr : ∫ y : ℝ, y * Real.sin (2 * π * y) * gaussWeight y =
      ∫ y : ℝ, y * gaussWeight y * Real.sin (2 * π * y) := by
    congr 1; ext y; ring
  rw [hr]
  rw [hcos] at hl
  linarith [hibp, hl]

theorem integral_mul_gaussWeight : ∫ y : ℝ, y * gaussWeight y = 0 := by
  have hint_g : Integrable gaussWeight := by
    have := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    unfold gaussWeight; ring_nf
  have hint_yg : Integrable (fun y : ℝ => y * gaussWeight y) := by
    have := integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    unfold gaussWeight; ring_nf
  have hu : ∀ y : ℝ, HasDerivAt (fun y => -gaussWeight y) (y * gaussWeight y) y := by
    intro y
    have h := ((hasDerivAt_pow 2 y).neg.div_const 2).exp.neg
    refine h.congr_deriv ?_
    unfold gaussWeight
    simp only [Pi.neg_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring_nf
  have hv : ∀ y : ℝ, HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := fun y => hasDerivAt_const y 1
  have h1 : Integrable ((fun y => -gaussWeight y) * fun _ => (0 : ℝ)) := by
    have e : ((fun y => -gaussWeight y) * fun _ => (0 : ℝ)) = 0 := by ext y; simp
    rw [e]; exact integrable_zero _ _ _
  have h2 : Integrable ((fun y => y * gaussWeight y) * fun _ => (1 : ℝ)) := by
    have e : ((fun y => y * gaussWeight y) * fun _ => (1 : ℝ)) = fun y => y * gaussWeight y := by
      ext y; simp
    rw [e]; exact hint_yg
  have h3 : Integrable ((fun y => -gaussWeight y) * fun _ => (1 : ℝ)) := by
    have e : ((fun y => -gaussWeight y) * fun _ => (1 : ℝ)) = fun y => -gaussWeight y := by
      ext y; simp
    rw [e]; exact hint_g.neg
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun y => -gaussWeight y)
    (v := fun _ => (1 : ℝ)) (u' := fun y => y * gaussWeight y) (v' := fun _ => 0)
    (fun y _ => hu y) (fun y _ => hv y) h1 h2 h3
  simp only [mul_zero, integral_zero, mul_one] at h
  linarith

/-- **Moments do not determine the log-mean.** Two probability densities of `Y = log X` share
every exponential moment `E e^{kY}` (`k ∈ ℤ`), i.e. every integer moment of `X`, while their means
`E Y = E log X` differ by `2π e^{−2π²}`. -/
theorem logNormal_moments_do_not_determine_logMean :
    ∃ f₁ f₂ : ℝ → ℝ, (∀ y, 0 ≤ f₁ y) ∧ (∀ y, 0 ≤ f₂ y) ∧
      (∀ k : ℤ, ∫ y, Real.exp (k * y) * f₁ y = ∫ y, Real.exp (k * y) * f₂ y) ∧
      (∫ y, y * f₂ y) - (∫ y, y * f₁ y) = 2 * π * Real.exp (-(2 * π ^ 2)) := by
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨fun y => gaussWeight y / Real.sqrt (2 * π),
    fun y => gaussWeight y * (1 + Real.sin (2 * π * y)) / Real.sqrt (2 * π),
    fun y => div_nonneg (gaussWeight_pos y).le hs.le,
    fun y => div_nonneg (mul_nonneg (gaussWeight_pos y).le
      (by linarith [Real.neg_one_le_sin (2 * π * y)])) hs.le, ?_, ?_⟩
  · intro k
    have hint_e : Integrable (fun y : ℝ => Real.exp (k * y) * gaussWeight y) := by
      have := (integrable_cexp_gauss (((k : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      rw [RCLike.re_to_complex, cexp_gauss_real_mul_I, Complex.re_ofReal_mul]
      simp
    have hint_s : Integrable (fun y : ℝ => Real.exp (k * y) * Real.sin (2 * π * y) *
        gaussWeight y) := by
      refine hint_e.mono' ?_ ?_
      · exact (by fun_prop : Continuous fun y : ℝ => Real.exp (k * y) * Real.sin (2 * π * y) *
          gaussWeight y).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun y => ?_
        rw [Real.norm_eq_abs, show Real.exp (k * y) * Real.sin (2 * π * y) * gaussWeight y =
          (Real.exp (k * y) * gaussWeight y) * Real.sin (2 * π * y) by ring, abs_mul,
          abs_of_pos (mul_pos (Real.exp_pos _) (gaussWeight_pos y))]
        exact mul_le_of_le_one_right (mul_pos (Real.exp_pos _) (gaussWeight_pos y)).le
          (Real.abs_sin_le_one _)
    have hsplit : ∀ y : ℝ, Real.exp (k * y) *
        (gaussWeight y * (1 + Real.sin (2 * π * y)) / Real.sqrt (2 * π)) =
        Real.exp (k * y) * gaussWeight y / Real.sqrt (2 * π) +
          Real.exp (k * y) * Real.sin (2 * π * y) * gaussWeight y / Real.sqrt (2 * π) := by
      intro y; ring
    simp_rw [hsplit]
    rw [integral_add (hint_e.div_const _) (hint_s.div_const _), integral_div (μ := volume)
      (fun y => Real.exp (k * y) * Real.sin (2 * π * y) * gaussWeight y),
      integral_exp_mul_sin_gaussWeight, zero_div, add_zero]
    congr 1; ext y; ring
  · have hint_yg : Integrable (fun y : ℝ => y * gaussWeight y) := by
      have := integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      unfold gaussWeight; ring_nf
    have hint_ys : Integrable (fun y : ℝ => y * Real.sin (2 * π * y) * gaussWeight y) := by
      refine hint_yg.norm.mono' ?_ ?_
      · exact (by fun_prop : Continuous fun y : ℝ => y * Real.sin (2 * π * y) *
          gaussWeight y).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun y => ?_
        rw [show y * Real.sin (2 * π * y) * gaussWeight y =
          (y * gaussWeight y) * Real.sin (2 * π * y) by ring, norm_mul,
          Real.norm_eq_abs (Real.sin _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
    have h2 : ∀ y : ℝ, y * (gaussWeight y * (1 + Real.sin (2 * π * y)) / Real.sqrt (2 * π)) =
        y * gaussWeight y / Real.sqrt (2 * π) +
          y * Real.sin (2 * π * y) * gaussWeight y / Real.sqrt (2 * π) := by
      intro y; ring
    have h1 : ∀ y : ℝ, y * (gaussWeight y / Real.sqrt (2 * π)) =
        y * gaussWeight y / Real.sqrt (2 * π) := by
      intro y; ring
    simp_rw [h2, h1]
    rw [integral_add (hint_yg.div_const _) (hint_ys.div_const _),
      integral_div (μ := volume) (fun y => y * gaussWeight y),
      integral_div (μ := volume) (fun y => y * Real.sin (2 * π * y) * gaussWeight y),
      integral_mul_gaussWeight, integral_mul_sin_gaussWeight]
    field_simp

end

end GaloisForLFunctions.RHTower.WD
