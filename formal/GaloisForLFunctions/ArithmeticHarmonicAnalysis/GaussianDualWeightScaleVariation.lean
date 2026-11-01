import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualWeightConductor

/-! # Scale variation of the exact Gaussian dual weight

The Mellin kernel's denominator cancels the scale derivative of its power.
Integrating the resulting difference estimate gives conductor-scale variation
on dyadic intervals, without differentiating the contour integral.
-/

noncomputable section
open Complex MeasureTheory Set RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The scale derivative cancels the Mellin kernel's simple pole. -/
theorem hasDerivAt_smoothAFEMellinIntegrand_scale {w : ℂ} (hw : w ≠ 0)
    {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun y : ℝ => smoothAFEMellinIntegrand y w)
      (-((Y : ℂ) ^ (-w - 1)) * Complex.exp (w ^ 2)) Y := by
  refine ((hasDerivAt_ofReal_cpow_neg_highBlockCutoffMonotone (w := w) hY).mul_const
    (smoothAFEGaussianKernel w)).congr_deriv ?_
  unfold smoothAFEGaussianKernel
  field_simp [hw]

/-- Gaussian decay survives the scale difference with no frequency loss. -/
theorem norm_smoothAFEMellinIntegrand_sub_le {σ a b : ℝ}
    (hσ : -1 ≤ σ) (hσ0 : σ ≠ 0) (ha : 0 < a) (hab : a ≤ b) (v : ℝ) :
    ‖smoothAFEMellinIntegrand b ((σ : ℂ) + (v : ℂ) * I) -
        smoothAFEMellinIntegrand a ((σ : ℂ) + (v : ℂ) * I)‖ ≤
      (a ^ (-σ - 1) * Real.exp (σ ^ 2) * Real.exp (-(v ^ 2))) * (b - a) := by
  let w : ℂ := (σ : ℂ) + (v : ℂ) * I
  have hw : w ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    exact hσ0 (by simpa only [w, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.zero_re] using hre)
  have hwr : w.re = σ := by simp only [w, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hnorm : ‖Complex.exp (w ^ 2)‖ = Real.exp (σ ^ 2) * Real.exp (-(v ^ 2)) := by
    rw [Complex.norm_exp]
    have hre : (w ^ 2).re = σ ^ 2 + -(v ^ 2) := by
      simp only [w, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, I_re, I_im]
      ring
    rw [hre, Real.exp_add]
  have hd : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun y : ℝ => smoothAFEMellinIntegrand y w)
        (-((x : ℂ) ^ (-w - 1)) * Complex.exp (w ^ 2)) (Icc a b) x :=
    fun x hx => (hasDerivAt_smoothAFEMellinIntegrand_scale hw (ha.trans_le hx.1)).hasDerivWithinAt
  have hb : ∀ x ∈ Ico a b,
      ‖-((x : ℂ) ^ (-w - 1)) * Complex.exp (w ^ 2)‖ ≤
        a ^ (-σ - 1) * Real.exp (σ ^ 2) * Real.exp (-(v ^ 2)) := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1), hnorm]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, hwr]
    calc x ^ (-σ - 1) * (Real.exp (σ ^ 2) * Real.exp (-(v ^ 2))) ≤
        a ^ (-σ - 1) * (Real.exp (σ ^ 2) * Real.exp (-(v ^ 2))) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith only [hσ])) (by positivity)
      _ = _ := by ring
  exact norm_image_sub_le_of_norm_deriv_le_segment' hd hb b (right_mem_Icc.2 hab)

/-- The positive contour gives reciprocal-square scale variation. -/
theorem exists_norm_dualWeight_sub_le_positive_scale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {a b : ℝ}, 0 < a → a ≤ b →
      ‖smoothAFEZetaDualWeight τ b - smoothAFEZetaDualWeight τ a‖ ≤
        C * (1 + |τ|) * a ^ (-2 : ℝ) * (b - a) := by
  let G : ℝ := ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let C : ℝ := (1 / (2 * Real.pi)) * Real.exp 1 * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  refine ⟨C, by dsimp only [C]; positivity, fun τ a b ha hab => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  let F : ℝ → ℝ → ℂ := fun Y v =>
    smoothAFEZetaChiShiftRatio (linePt τ) (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  have hFa : Integrable (F a) := smoothAFEZetaDualWeightAt_one_integrable ha τ
  have hFb : Integrable (F b) := smoothAFEZetaDualWeightAt_one_integrable hb τ
  let D : ℝ := (1 + |τ|) * a ^ (-2 : ℝ) * Real.exp 1 * (b - a)
  have hmajor : Integrable (fun v : ℝ => D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hpoint (v : ℝ) : ‖F b v - F a v‖ ≤ D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    have hm := norm_smoothAFEMellinIntegrand_sub_le (σ := 1) (by norm_num)
      (by norm_num) ha hab v
    norm_num only at hm
    have hr := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le τ v
    dsimp only [F]
    rw [← mul_sub, norm_mul]
    calc _ ≤ ((1 + |τ|) * (1 + |v|)) *
        ((a ^ (-2 : ℝ) * Real.exp 1 * Real.exp (-(v ^ 2))) * (b - a)) := by
          exact mul_le_mul hr hm (norm_nonneg _) (by positivity)
      _ = _ := by dsimp only [D]; ring
  have heq : smoothAFEZetaDualWeight τ b - smoothAFEZetaDualWeight τ a =
      (1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ, (F b v - F a v) := by
    unfold smoothAFEZetaDualWeight
    rw [← smul_sub, integral_sub hFb hFa]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  calc _ ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖F b v - F a v‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono_ae (hFb.sub hFa).norm hmajor (Filter.Eventually.of_forall hpoint)
    _ = _ := by rw [integral_const_mul]; dsimp only [C, D, G]; ring

/-- The negative contour gives conductor-normalized variation below the conductor. -/
theorem exists_norm_dualWeight_sub_le_negative_scale {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) {a b : ℝ}, 0 < a → a ≤ b →
      ‖smoothAFEZetaDualWeight τ b - smoothAFEZetaDualWeight τ a‖ ≤
        C * a ^ (δ - 1) / (max 1 |τ|) ^ δ * (b - a) := by
  obtain ⟨K, hK, hratio⟩ := exists_norm_smoothAFEZetaChiShiftRatio_pos_le hδ hδhalf
  let G : ℝ := ∫ v : ℝ, (1 + |v|) * Real.exp (-(v ^ 2))
  let C : ℝ := (1 / (2 * Real.pi)) * K * Real.exp (δ ^ 2) * G
  have hG : 0 ≤ G := integral_nonneg fun v => by positivity
  refine ⟨C, by dsimp only [C]; positivity, fun τ a b ha hab => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  let F : ℝ → ℝ → ℂ := fun Y v =>
    smoothAFEZetaChiShiftRatio (linePt τ) (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((-δ : ℝ) : ℂ) + (v : ℂ) * I)
  have hFa : Integrable (F a) := smoothAFEZetaDualWeightAt_neg_integrable hδ hδhalf ha τ
  have hFb : Integrable (F b) := smoothAFEZetaDualWeightAt_neg_integrable hδ hδhalf hb τ
  let D : ℝ := K * a ^ (δ - 1) / (max 1 |τ|) ^ δ * Real.exp (δ ^ 2) * (b - a)
  have hmajor : Integrable (fun v : ℝ => D * ((1 + |v|) * Real.exp (-(v ^ 2)))) :=
    integrable_one_add_abs_mul_exp_neg_sq.const_mul D
  have hpoint (v : ℝ) : ‖F b v - F a v‖ ≤ D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
    have hm := norm_smoothAFEMellinIntegrand_sub_le (σ := -δ) (by linarith only [hδhalf])
      (neg_ne_zero.mpr hδ.ne') ha hab v
    simp only [neg_neg, neg_sq] at hm
    have hr := hratio τ v
    have hvpow : (1 + |v|) ^ δ ≤ 1 + |v| := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by linarith only [abs_nonneg v] : 1 ≤ 1 + |v|) (by linarith only [hδhalf] : δ ≤ 1)
    have hr' : ‖smoothAFEZetaChiShiftRatio (linePt τ)
        (-(((-δ : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * (1 + |v|) / (max 1 |τ|) ^ δ :=
      hr.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvpow hK) (by positivity))
    dsimp only [F]
    rw [← mul_sub, norm_mul]
    calc _ ≤ (K * (1 + |v|) / (max 1 |τ|) ^ δ) *
        ((a ^ (δ - 1) * Real.exp (δ ^ 2) * Real.exp (-(v ^ 2))) * (b - a)) :=
          mul_le_mul hr' hm (norm_nonneg _) (by positivity)
      _ = _ := by dsimp only [D]; ring
  have heq : smoothAFEZetaDualWeight τ b - smoothAFEZetaDualWeight τ a =
      (1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ, (F b v - F a v) := by
    calc _ = smoothAFEZetaDualWeightAt (-δ) τ b - smoothAFEZetaDualWeightAt (-δ) τ a := by
          rw [smoothAFEZetaDualWeight_eq_one_add_at_neg hδ hδhalf hb τ,
            smoothAFEZetaDualWeight_eq_one_add_at_neg hδ hδhalf ha τ]
          ring
      _ = _ := by
        unfold smoothAFEZetaDualWeightAt
        rw [← smul_sub, integral_sub hFb hFa]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  calc _ ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, ‖F b v - F a v‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * ∫ v : ℝ, D * ((1 + |v|) * Real.exp (-(v ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono_ae (hFb.sub hFa).norm hmajor (Filter.Eventually.of_forall hpoint)
    _ = _ := by rw [integral_const_mul]; dsimp only [C, D, G]; ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_dualWeight_sub_le_positive_scale

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_dualWeight_sub_le_negative_scale
