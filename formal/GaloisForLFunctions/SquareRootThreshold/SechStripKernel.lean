import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# A positive analytic weight on a vertical strip

The reciprocal cosine is positive in real part throughout its pole-free strip.
Its vertical integral has real part `2a`, independently of the horizontal
shift. Exponential decay supplies the first absolute moment used in weighted
logarithmic-derivative contours.
-/

open Complex Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.SquareRootThreshold

noncomputable section

def sechStripWeight (a T : ℝ) (s : ℂ) : ℂ :=
  (Complex.cos (((Real.pi / (2 * a) : ℝ) : ℂ) * (s - (1 / 2 + (T : ℂ) * I))))⁻¹

private theorem cos_re_formula (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re, Complex.cosh_ofReal_re, Complex.sinh_ofReal_re]

private theorem scaled_depth_lt {a x : ℝ} (ha : 0 < a) (hx : |x| < a) :
    |Real.pi / (2 * a) * x| < Real.pi / 2 := by
  rw [abs_mul, abs_of_pos (by positivity : 0 < Real.pi / (2 * a))]
  calc
    Real.pi / (2 * a) * |x| < Real.pi / (2 * a) * a :=
      mul_lt_mul_of_pos_left hx (by positivity)
    _ = Real.pi / 2 := by field_simp

theorem re_cos_sechStripWeight_pos {a T : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : |s.re - 1 / 2| < a) :
    0 < (Complex.cos (((Real.pi / (2 * a) : ℝ) : ℂ) *
      (s - (1 / 2 + (T : ℂ) * I)))).re := by
  rw [cos_re_formula]
  have hre : ((((Real.pi / (2 * a) : ℝ) : ℂ) *
      (s - (1 / 2 + (T : ℂ) * I)))).re =
      Real.pi / (2 * a) * (s.re - 1 / 2) := by
    norm_num only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.add_re, Complex.I_re, Complex.I_im,
      Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num
  rw [hre]
  exact mul_pos (Real.cos_pos_of_mem_Ioo (abs_lt.mp (scaled_depth_lt ha hs))) (Real.cosh_pos _)

theorem sechStripWeight_re_pos {a T : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : |s.re - 1 / 2| < a) : 0 < (sechStripWeight a T s).re := by
  have hp := re_cos_sechStripWeight_pos (T := T) ha hs
  have hne : Complex.cos (((Real.pi / (2 * a) : ℝ) : ℂ) *
      (s - (1 / 2 + (T : ℂ) * I))) ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  rw [sechStripWeight, Complex.inv_re]
  exact div_pos hp (Complex.normSq_pos.mpr hne)

theorem sechStripWeight_same_height (a T : ℝ) {s : ℂ} (hs : s.im = T) :
    sechStripWeight a T s =
      ((Real.cos (Real.pi / (2 * a) * (s.re - 1 / 2)))⁻¹ : ℝ) := by
  have harg : (((Real.pi / (2 * a) : ℝ) : ℂ) *
      (s - (1 / 2 + (T : ℂ) * I))) =
      ((Real.pi / (2 * a) * (s.re - 1 / 2) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hs]
  rw [sechStripWeight, harg, ← Complex.ofReal_cos, ← Complex.ofReal_inv]

@[simp] theorem sechStripWeight_center (a T : ℝ) :
    sechStripWeight a T (1 / 2 + (T : ℂ) * I) = 1 := by
  simp [sechStripWeight]

theorem analyticOnNhd_sechStripWeight {a : ℝ} (ha : 0 < a) (T : ℝ) :
    AnalyticOnNhd ℂ (sechStripWeight a T) {s : ℂ | |s.re - 1 / 2| < a} := by
  intro s hs
  have hn : Complex.cos (((Real.pi / (2 * a) : ℝ) : ℂ) *
      (s - (1 / 2 + (T : ℂ) * I))) ≠ 0 := by
    intro h
    have hp := re_cos_sechStripWeight_pos (T := T) ha hs
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  unfold sechStripWeight
  have han : AnalyticAt ℂ (fun z : ℂ => Complex.cos
      (((Real.pi / (2 * a) : ℝ) : ℂ) * (z - (1 / 2 + (T : ℂ) * I)))) s := by
    fun_prop
  exact han.inv hn

theorem norm_sechStripWeight_le {a b T : ℝ} (hb : 0 ≤ b) (hba : b < a) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ b) :
    ‖sechStripWeight a T s‖ ≤
      (Real.cos (Real.pi / (2 * a) * b))⁻¹ /
        Real.cosh (Real.pi / (2 * a) * (s.im - T)) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hc : 0 < Real.pi / (2 * a) := by positivity
  have hangle : |Real.pi / (2 * a) * b| < Real.pi / 2 :=
    scaled_depth_lt ha (by simpa [abs_of_nonneg hb] using hba)
  have hcb : 0 < Real.cos (Real.pi / (2 * a) * b) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp hangle)
  have hcmp : Real.cos (Real.pi / (2 * a) * b) ≤
      Real.cos (Real.pi / (2 * a) * (s.re - 1 / 2)) := by
    rw [← Real.cos_abs (Real.pi / (2 * a) * (s.re - 1 / 2))]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    · have := (abs_lt.mp hangle).2
      linarith [Real.pi_pos]
    · rw [abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hs hc.le
  have hre : (Complex.cos (((Real.pi / (2 * a) : ℝ) : ℂ) *
      (s - (1 / 2 + (T : ℂ) * I)))).re =
      Real.cos (Real.pi / (2 * a) * (s.re - 1 / 2)) *
        Real.cosh (Real.pi / (2 * a) * (s.im - T)) := by
    rw [cos_re_formula]
    norm_num only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, sub_zero,
      zero_add, add_zero]
    norm_num
  have hlower : Real.cos (Real.pi / (2 * a) * b) *
      Real.cosh (Real.pi / (2 * a) * (s.im - T)) ≤
      ‖Complex.cos (((Real.pi / (2 * a) : ℝ) : ℂ) *
        (s - (1 / 2 + (T : ℂ) * I)))‖ := by
    calc
      _ ≤ Real.cos (Real.pi / (2 * a) * (s.re - 1 / 2)) *
          Real.cosh (Real.pi / (2 * a) * (s.im - T)) :=
        mul_le_mul_of_nonneg_right hcmp (Real.cosh_pos _).le
      _ = _ := hre.symm
      _ ≤ _ := Complex.re_le_norm _
  rw [sechStripWeight, norm_inv]
  calc
    _ ≤ (Real.cos (Real.pi / (2 * a) * b) *
        Real.cosh (Real.pi / (2 * a) * (s.im - T)))⁻¹ :=
      inv_anti₀ (mul_pos hcb (Real.cosh_pos _)) hlower
    _ = _ := by simp only [mul_inv, div_eq_mul_inv]

theorem re_inv_cos_add_mul_I (θ y : ℝ) :
    ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re =
      Real.cos θ * Real.cosh y / (Real.cos θ ^ 2 + Real.sinh y ^ 2) := by
  have hr : (Complex.cos ((θ : ℂ) + (y : ℂ) * I)).re =
      Real.cos θ * Real.cosh y := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cosh_ofReal_re]
  have hi : (Complex.cos ((θ : ℂ) + (y : ℂ) * I)).im =
      -(Real.sin θ * Real.sinh y) := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re, Complex.sinh_ofReal_re]
  rw [Complex.inv_re, Complex.normSq_apply, hr, hi]
  simp only [← sq, neg_sq]
  have hden : (Real.cos θ * Real.cosh y) ^ 2 + (Real.sin θ * Real.sinh y) ^ 2 =
      Real.cos θ ^ 2 + Real.sinh y ^ 2 := by
    linear_combination
      (Real.cos θ ^ 2) * (Real.cosh_sq_sub_sinh_sq y) +
      (Real.sinh y ^ 2) * (Real.cos_sq_add_sin_sq θ)
  rw [hden]

theorem hasDerivAt_arctan_sinh_div_cos {θ : ℝ} (hθ : 0 < Real.cos θ) (y : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arctan (Real.sinh x / Real.cos θ))
      (((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re) y := by
  have h := (Real.hasDerivAt_arctan (Real.sinh y / Real.cos θ)).comp y
    ((Real.hasDerivAt_sinh y).div_const (Real.cos θ))
  have heq : ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re =
      1 / (1 + (Real.sinh y / Real.cos θ) ^ 2) * (Real.cosh y / Real.cos θ) := by
    rw [re_inv_cos_add_mul_I]
    field_simp
  rw [heq]
  exact h

private theorem norm_inv_cos_add_mul_I_le {θ : ℝ} (hθ : 0 < Real.cos θ) (y : ℝ) :
    ‖(Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹‖ ≤
      (2 / Real.cos θ) * Real.exp (-|y|) := by
  have hr : (Complex.cos ((θ : ℂ) + (y : ℂ) * I)).re =
      Real.cos θ * Real.cosh y := by
    rw [Complex.cos_add_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cosh_ofReal_re]
  have hlower : Real.cos θ * Real.cosh y ≤
      ‖Complex.cos ((θ : ℂ) + (y : ℂ) * I)‖ := by
    rw [← hr]
    exact Complex.re_le_norm _
  have he : Real.exp |y| ≤ 2 * Real.cosh y := by
    rw [Real.cosh_eq]
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      linarith [Real.exp_pos (-y)]
    · rw [abs_of_nonpos hy]
      linarith [Real.exp_pos y]
  have heprod : Real.exp (-|y|) * Real.exp |y| = 1 := by
    rw [← Real.exp_add]
    simp
  have hcosh : (Real.cosh y)⁻¹ ≤ 2 * Real.exp (-|y|) := by
    rw [inv_eq_one_div, div_le_iff₀ (Real.cosh_pos y)]
    have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (-|y|)).le
    rw [heprod] at hmul
    nlinarith only [hmul]
  rw [norm_inv]
  calc
    _ ≤ (Real.cos θ * Real.cosh y)⁻¹ :=
      inv_anti₀ (mul_pos hθ (Real.cosh_pos y)) hlower
    _ = (Real.cos θ)⁻¹ * (Real.cosh y)⁻¹ := mul_inv _ _
    _ ≤ (Real.cos θ)⁻¹ * (2 * Real.exp (-|y|)) :=
      mul_le_mul_of_nonneg_left hcosh (inv_nonneg.mpr hθ.le)
    _ = _ := by ring

theorem integrable_inv_cos_add_mul_I {θ : ℝ} (hθ : 0 < Real.cos θ) :
    Integrable (fun y : ℝ => (Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹) := by
  have hne : ∀ y : ℝ, Complex.cos ((θ : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hzero
    have hr : (Complex.cos ((θ : ℂ) + (y : ℂ) * I)).re =
        Real.cos θ * Real.cosh y := by
      rw [Complex.cos_add_mul_I]
      simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cosh_ofReal_re]
    rw [hzero, Complex.zero_re] at hr
    exact (mul_pos hθ (Real.cosh_pos y)).ne' hr.symm
  have hcont : Continuous (fun y : ℝ => (Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹) := by
    exact Continuous.inv₀ (by fun_prop) hne
  have hint : Integrable (fun y : ℝ => Real.exp (-|y|)) := by
    simpa only [one_mul] using RHTower.integrable_exp_neg_mul_abs' (c := 1) zero_lt_one
  exact (hint.const_mul (2 / Real.cos θ)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall (norm_inv_cos_add_mul_I_le hθ))

private theorem sinh_tendsto_atTop : Tendsto Real.sinh atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    eventually_ge_atTop (Real.log (2 * max B 0 + 1))] with y hy0 hy
  have hp : 0 < 2 * max B 0 + 1 := by positivity
  have he := Real.exp_le_exp.mpr hy
  rw [Real.exp_log hp] at he
  have hne : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hy0])
  rw [Real.sinh_eq]
  linarith only [he, hne, le_max_left B 0]

theorem integral_re_inv_cos_add_mul_I {θ : ℝ} (hθ : 0 < Real.cos θ) :
    (∫ y : ℝ, ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re) = Real.pi := by
  have hint := (integrable_inv_cos_add_mul_I hθ).re
  have hsinh : Tendsto (fun y : ℝ => Real.sinh y / Real.cos θ) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    filter_upwards [(Filter.tendsto_atTop.1 sinh_tendsto_atTop) (B * Real.cos θ)] with y hy
    exact (le_div_iff₀ hθ).mpr hy
  have hatan : Tendsto (fun y : ℝ => Real.arctan (Real.sinh y / Real.cos θ))
      atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hsinh
  have hfinite : ∀ R : ℝ,
      (∫ y in (-R)..R, ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re) =
        2 * Real.arctan (Real.sinh R / Real.cos θ) := by
    intro R
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_arctan_sinh_div_cos hθ y) hint.intervalIntegrable]
    simp [Real.sinh_neg, neg_div, Real.arctan_neg]
    ring
  have hi := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  change Tendsto (fun R : ℝ => ∫ y in (-R)..R,
      ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re) atTop
    (𝓝 (∫ y : ℝ, ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re)) at hi
  have hb : Tendsto (fun R : ℝ => 2 * Real.arctan (Real.sinh R / Real.cos θ))
      atTop (𝓝 Real.pi) := by
    convert hatan.const_mul 2 using 1; ring
  have heq : (fun R : ℝ => ∫ y in (-R)..R,
      ((Complex.cos ((θ : ℂ) + (y : ℂ) * I))⁻¹).re) =
      fun R : ℝ => 2 * Real.arctan (Real.sinh R / Real.cos θ) := funext hfinite
  rw [heq] at hi
  exact tendsto_nhds_unique hi hb

theorem sechStripWeight_vertical (a b T u : ℝ) :
    sechStripWeight a T (1 / 2 + (b : ℂ) + ((T + u : ℝ) : ℂ) * I) =
      (Complex.cos (((Real.pi / (2 * a) * b : ℝ) : ℂ) +
        ((Real.pi / (2 * a) * u : ℝ) : ℂ) * I))⁻¹ := by
  unfold sechStripWeight
  congr 2
  push_cast
  ring

theorem integral_re_sechStripWeight_vertical {a b : ℝ} (ha : 0 < a) (hb : |b| < a) :
    (∫ u : ℝ, (sechStripWeight a 0 (1 / 2 + (b : ℂ) + (u : ℂ) * I)).re) =
      2 * a := by
  have hc : 0 < Real.pi / (2 * a) := by positivity
  have hθ : 0 < Real.cos (Real.pi / (2 * a) * b) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp (scaled_depth_lt ha hb))
  have hfun : (fun u : ℝ =>
      (sechStripWeight a 0 (1 / 2 + (b : ℂ) + (u : ℂ) * I)).re) =
      fun u : ℝ => ((Complex.cos (((Real.pi / (2 * a) * b : ℝ) : ℂ) +
        ((Real.pi / (2 * a) * u : ℝ) : ℂ) * I))⁻¹).re := by
    funext u
    simpa only [zero_add] using congrArg Complex.re (sechStripWeight_vertical a b 0 u)
  rw [hfun]
  rw [Measure.integral_comp_mul_left
    (fun y : ℝ => ((Complex.cos (((Real.pi / (2 * a) * b : ℝ) : ℂ) + (y : ℂ) * I))⁻¹).re)
    (Real.pi / (2 * a))]
  rw [integral_re_inv_cos_add_mul_I hθ, smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]
  field_simp

/-- The secant strip kernel has exponential decay uniformly on every narrower strip. -/
theorem norm_sechStripWeight_le_exp {a b T : ℝ} (hb : 0 ≤ b) (hba : b < a) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ b) :
    ‖sechStripWeight a T s‖ ≤
      (2 / Real.cos (Real.pi / (2 * a) * b)) *
        Real.exp (-(Real.pi / (2 * a) * |s.im - T|)) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hc : 0 < Real.pi / (2 * a) := by positivity
  have hcos : 0 < Real.cos (Real.pi / (2 * a) * b) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp (scaled_depth_lt ha
      (by simpa only [abs_of_nonneg hb] using hba)))
  have hcosh (y : ℝ) : (Real.cosh y)⁻¹ ≤ 2 * Real.exp (-|y|) := by
    have he : Real.exp |y| ≤ 2 * Real.cosh y := by
      rw [Real.cosh_eq]
      rcases le_total 0 y with hy | hy
      · rw [abs_of_nonneg hy]
        linarith only [Real.exp_pos (-y)]
      · rw [abs_of_nonpos hy]
        linarith only [Real.exp_pos y]
    rw [inv_eq_one_div, div_le_iff₀ (Real.cosh_pos y)]
    have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (-|y|)).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    nlinarith only [hmul]
  calc
    _ ≤ (Real.cos (Real.pi / (2 * a) * b))⁻¹ *
        (Real.cosh (Real.pi / (2 * a) * (s.im - T)))⁻¹ := by
      simpa only [div_eq_mul_inv] using norm_sechStripWeight_le hb hba hs
    _ ≤ (Real.cos (Real.pi / (2 * a) * b))⁻¹ *
        (2 * Real.exp (-|Real.pi / (2 * a) * (s.im - T)|)) :=
      mul_le_mul_of_nonneg_left (hcosh _) (inv_nonneg.mpr hcos.le)
    _ = _ := by rw [abs_mul, abs_of_pos hc]; ring

private theorem integrable_abs_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => |u| * Real.exp (-(c * |u|))) := by
  have hc2 : 0 < c / 2 := by positivity
  refine ((RHTower.integrable_exp_neg_mul_abs' hc2).const_mul (2 / c)).mono'
    (by fun_prop) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hpoly : |u| ≤ (2 / c) * Real.exp (c / 2 * |u|) := by
    have he := Real.add_one_le_exp (c / 2 * |u|)
    calc
      |u| ≤ (2 * Real.exp (c / 2 * |u|)) / c :=
        (le_div_iff₀ hc).mpr (by linarith only [he])
      _ = _ := by ring
  calc
    _ ≤ ((2 / c) * Real.exp (c / 2 * |u|)) * Real.exp (-(c * |u|)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The shifted kernel is integrable against the linear weight needed for logarithmic
convolutions, since its first absolute moment is finite. -/
theorem integrable_norm_sechStripWeight_vertical_weight {a b : ℝ}
    (ha : 0 < a) (hb : |b| < a) :
    Integrable (fun u : ℝ =>
      ‖sechStripWeight a 0 (1 / 2 + (b : ℂ) + (u : ℂ) * I)‖ *
        (2 + |u| / Real.log 2)) := by
  have hc : 0 < Real.pi / (2 * a) := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : Continuous (fun u : ℝ =>
      sechStripWeight a 0 (1 / 2 + (b : ℂ) + (u : ℂ) * I)) := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    exact ((analyticOnNhd_sechStripWeight ha 0 _
      (by simpa using hb)).continuousAt).comp (by fun_prop)
  have hmajor := (((RHTower.integrable_exp_neg_mul_abs' hc).const_mul 2).add
    ((integrable_abs_mul_exp_neg_mul_abs hc).div_const (Real.log 2))).const_mul
      (2 / Real.cos (Real.pi / (2 * a) * |b|))
  refine hmajor.mono' (by fun_prop) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
  have h := norm_sechStripWeight_le_exp (T := 0) (abs_nonneg b) hb
    (s := 1 / 2 + (b : ℂ) + (u : ℂ) * I) (by simp)
  norm_num at h
  calc
    _ ≤ ((2 / Real.cos (Real.pi / (2 * a) * |b|)) *
        Real.exp (-(Real.pi / (2 * a) * |u|))) * (2 + |u| / Real.log 2) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by dsimp only [Pi.add_apply]; ring

end
end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.sechStripWeight_re_pos
#print axioms GaloisForLFunctions.SquareRootThreshold.integral_re_sechStripWeight_vertical
#print axioms GaloisForLFunctions.SquareRootThreshold.norm_sechStripWeight_le_exp
#print axioms GaloisForLFunctions.SquareRootThreshold.integrable_norm_sechStripWeight_vertical_weight
