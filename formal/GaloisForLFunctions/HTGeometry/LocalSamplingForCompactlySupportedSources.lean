import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# A localised sampling bound for transforms of compactly supported sources

For `f` supported in `[−a, a]` the transform `Φ = 𝓕 f` reproduces itself against a fixed
integrable kernel of quadratic decay: `Φ = Φ ⋆ G_a` with `G_a = 𝓕 T_a`, where `T_a` is the
trapezoidal cutoff `(2a)⁻¹ (1_{[−a,a]} ⋆ 1_{[−2a,2a]})`, identically one on `[−a, a]`.  The
kernel is the product of two box transforms, hence `|G_a(x)| ≲ (8a + a⁻¹)/(1+x²)`.

Cauchy–Schwarz then turns the reproducing identity into a **local** bound

`|Φ(x₀)|² ≤ ‖G_a‖₁ ∫ |Φ(x)|² |G_a(x₀ − x)| dx`,

which localises the pointwise size of `Φ` at the unit scale with quadratically decaying tails —
the form needed to sample `Φ` on a point set of logarithmic density against a slowly varying
weight.
-/

open MeasureTheory Set Real Complex
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.LocalSampling

noncomputable section
set_option autoImplicit false

/-! ## The box and the trapezoidal cutoff -/

/-- The indicator of `[−p, p]`, as a complex-valued source. -/
def boxFn (p : ℝ) : ℝ → ℂ := (Icc (-p) p).indicator 1

theorem boxFn_apply (p t : ℝ) : boxFn p t = if t ∈ Icc (-p) p then 1 else 0 := by
  unfold boxFn
  by_cases h : t ∈ Icc (-p) p <;> simp [h]

theorem integrable_boxFn (p : ℝ) : Integrable (boxFn p) := by
  unfold boxFn
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (hs := measure_Icc_lt_top.ne)

theorem norm_boxFn_le (p t : ℝ) : ‖boxFn p t‖ ≤ 1 := by
  rw [boxFn_apply]
  by_cases h : t ∈ Icc (-p) p <;> simp [h]

/-- The convolution of two symmetric boxes is the length of the overlapping interval. -/
theorem convolution_boxFn (a t : ℝ) :
    convolution (boxFn a) (boxFn (2 * a)) (ContinuousLinearMap.mul ℂ ℂ) volume t =
      ((max 0 (min a (t + 2 * a) - max (-a) (t - 2 * a)) : ℝ) : ℂ) := by
  have hint : ∀ s : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (boxFn a s) (boxFn (2 * a) (t - s)) =
      (Icc (max (-a) (t - 2 * a)) (min a (t + 2 * a))).indicator (fun _ => (1:ℂ)) s := by
    intro s
    rw [ContinuousLinearMap.mul_apply', boxFn_apply, boxFn_apply, Set.indicator_apply]
    by_cases h1 : s ∈ Icc (-a) a
    · rw [Set.mem_Icc] at h1
      by_cases h2 : t - s ∈ Icc (-(2 * a)) (2 * a)
      · rw [Set.mem_Icc] at h2
        have hmem : s ∈ Icc (max (-a) (t - 2 * a)) (min a (t + 2 * a)) := by
          rw [Set.mem_Icc, max_le_iff, le_min_iff]
          exact ⟨⟨h1.1, by linarith [h2.2]⟩, h1.2, by linarith [h2.1]⟩
        rw [if_pos (Set.mem_Icc.mpr h1), if_pos (Set.mem_Icc.mpr h2), if_pos hmem]
        norm_num
      · have hnot : s ∉ Icc (max (-a) (t - 2 * a)) (min a (t + 2 * a)) := by
          intro hc
          rw [Set.mem_Icc] at hc
          have hb1 : t - 2 * a ≤ s := le_trans (le_max_right _ _) hc.1
          have hb2 : s ≤ t + 2 * a := le_trans hc.2 (min_le_right _ _)
          exact h2 (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        rw [if_pos (Set.mem_Icc.mpr h1), if_neg h2, if_neg hnot]
        norm_num
    · have hnot : s ∉ Icc (max (-a) (t - 2 * a)) (min a (t + 2 * a)) := by
        intro hc
        rw [Set.mem_Icc] at hc
        have hb1 : -a ≤ s := le_trans (le_max_left _ _) hc.1
        have hb2 : s ≤ a := le_trans hc.2 (min_le_left _ _)
        exact h1 (Set.mem_Icc.mpr ⟨hb1, hb2⟩)
      rw [if_neg h1, if_neg hnot]
      norm_num
  have hconv : convolution (boxFn a) (boxFn (2 * a)) (ContinuousLinearMap.mul ℂ ℂ) volume t =
      ∫ s : ℝ, (Icc (max (-a) (t - 2 * a)) (min a (t + 2 * a))).indicator (fun _ => (1:ℂ)) s :=
    integral_congr_ae (Filter.Eventually.of_forall hint)
  have hvol : volume.real (Icc (max (-a) (t - 2 * a)) (min a (t + 2 * a))) =
      max 0 (min a (t + 2 * a) - max (-a) (t - 2 * a)) := by
    rw [MeasureTheory.Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal']
    exact max_comm _ _
  rw [hconv, MeasureTheory.integral_indicator_const (1:ℂ) measurableSet_Icc,
    Complex.real_smul, mul_one, hvol]

/-- The trapezoidal cutoff: one on `[−a, a]`, supported in `[−3a, 3a]`. -/
def trapFn (a : ℝ) : ℝ → ℂ := fun t =>
  ((2 * a)⁻¹ : ℂ) * convolution (boxFn a) (boxFn (2 * a)) (ContinuousLinearMap.mul ℂ ℂ) volume t

theorem trapFn_eq (a t : ℝ) :
    trapFn a t = (((2 * a)⁻¹ * max 0 (min a (t + 2 * a) - max (-a) (t - 2 * a)) : ℝ) : ℂ) := by
  rw [trapFn, convolution_boxFn]
  push_cast
  ring

/-- The cutoff is identically one on the support interval. -/
theorem trapFn_eq_one {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : |t| ≤ a) : trapFn a t = 1 := by
  rw [abs_le] at ht
  have h1 : min a (t + 2 * a) = a := min_eq_left (by linarith [ht.1])
  have h2 : max (-a) (t - 2 * a) = -a := max_eq_left (by linarith [ht.2])
  rw [trapFn_eq, h1, h2, max_eq_right (by linarith)]
  have hval : ((2 * a)⁻¹ * (a - -a) : ℝ) = 1 := by
    rw [show a - -a = 2 * a by ring]
    field_simp
  rw [hval]
  norm_num

/-- The cutoff vanishes off `[−3a, 3a]`. -/
theorem trapFn_eq_zero {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 3 * a < |t|) : trapFn a t = 0 := by
  rw [trapFn_eq]
  rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
  · have h1 : min a (t + 2 * a) = a := min_eq_left (by rw [he] at ht; linarith)
    have h2 : max (-a) (t - 2 * a) = t - 2 * a := max_eq_right (by rw [he] at ht; linarith)
    rw [h1, h2, max_eq_left (by rw [he] at ht; linarith)]
    norm_num
  · have h1 : min a (t + 2 * a) = t + 2 * a := min_eq_right (by rw [he] at ht; linarith)
    have h2 : max (-a) (t - 2 * a) = -a := max_eq_left (by rw [he] at ht; linarith)
    rw [h1, h2, max_eq_left (by rw [he] at ht; linarith)]
    norm_num

theorem continuous_trapFn (a : ℝ) : Continuous (trapFn a) := by
  have : Continuous fun t : ℝ =>
      ((2 * a)⁻¹ * max 0 (min a (t + 2 * a) - max (-a) (t - 2 * a)) : ℝ) :=
    continuous_const.mul ((continuous_const.max
      ((continuous_const.min (continuous_id.add continuous_const)).sub
        (continuous_const.max (continuous_id.sub continuous_const)))))
  exact Complex.continuous_ofReal.comp this |>.congr fun t => (trapFn_eq a t).symm

theorem hasCompactSupport_trapFn {a : ℝ} (ha : 0 < a) : HasCompactSupport (trapFn a) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(3 * a)) (b := 3 * a))
  intro t ht
  refine trapFn_eq_zero ha ?_
  rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    · by_contra hcon
      exact ht (by constructor <;> [skip; skip] <;> simp at hcon ⊢ <;> linarith)

theorem integrable_trapFn {a : ℝ} (ha : 0 < a) : Integrable (trapFn a) :=
  (continuous_trapFn a).integrable_of_hasCompactSupport (hasCompactSupport_trapFn ha)

/-! ## The box transform and the quadratic decay of the kernel -/

theorem fourier_boxFn_eq (p x : ℝ) :
    𝓕 (boxFn p) x = ∫ t in Icc (-p) p, Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I * t) := by
  rw [Real.fourier_eq' (boxFn p) x]
  have h : ∀ t : ℝ, Complex.exp (((-2 * π * (inner ℝ t x : ℝ) : ℝ) : ℂ) * Complex.I) •
      boxFn p t = (Icc (-p) p).indicator
        (fun t : ℝ => Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I * t)) t := by
    intro t
    rw [boxFn_apply, Set.indicator_apply]
    by_cases ht : t ∈ Icc (-p) p
    · rw [if_pos ht, if_pos ht, smul_eq_mul, mul_one]
      congr 1
      push_cast [RCLike.inner_apply, conj_trivial]
      ring
    · rw [if_neg ht, if_neg ht, smul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_indicator measurableSet_Icc]

theorem norm_fourier_boxFn_le_two_mul {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    ‖𝓕 (boxFn p) x‖ ≤ 2 * p := by
  rw [fourier_boxFn_eq]
  have hbd : ∀ t ∈ Icc (-p) p,
      ‖Complex.exp (((-2 * π * x : ℝ) : ℂ) * Complex.I * t)‖ ≤ 1 := by
    intro t _
    rw [Complex.norm_exp]
    have : (((-2 * π * x : ℝ) : ℂ) * Complex.I * t).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have := norm_setIntegral_le_of_norm_le_const
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hbd
  refine this.trans ?_
  have hvol : volume.real (Icc (-p) p) = 2 * p := by
    rw [MeasureTheory.Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol, one_mul]

theorem norm_fourier_boxFn_le_inv {p : ℝ} (hp : 0 ≤ p) {x : ℝ} (hx : x ≠ 0) :
    ‖𝓕 (boxFn p) x‖ ≤ (π * |x|)⁻¹ := by
  have hne : (-2 * π * x : ℝ) ≠ 0 := by
    rcases hx.lt_or_gt with h | h
    · exact ne_of_gt (by nlinarith [Real.pi_pos])
    · exact ne_of_lt (by nlinarith [Real.pi_pos])
  have hc : ((-2 * π * x : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hne) Complex.I_ne_zero
  set c : ℂ := ((-2 * π * x : ℝ) : ℂ) * Complex.I with hcdef
  have hIcc : (∫ t in Icc (-p) p, Complex.exp (c * t)) = ∫ t in (-p)..p, Complex.exp (c * t) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  rw [fourier_boxFn_eq, hIcc, integral_exp_mul_complex hc]
  have hnum : ‖Complex.exp (c * ((p : ℝ) : ℂ)) - Complex.exp (c * ((-p : ℝ) : ℂ))‖ ≤ 2 := by
    have h1 : ‖Complex.exp (c * ((p : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, hcdef]
      norm_num [Complex.mul_re, Complex.mul_im]
    have h2 : ‖Complex.exp (c * ((-p : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, hcdef]
      norm_num [Complex.mul_re, Complex.mul_im]
    have h3 := norm_sub_le (Complex.exp (c * ((p : ℝ) : ℂ)))
      (Complex.exp (c * ((-p : ℝ) : ℂ)))
    rw [h1, h2] at h3
    linarith
  have hden : ‖c‖ = 2 * π * |x| := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_mul, abs_mul]
    simp [abs_of_pos Real.pi_pos]
  have hπx : 0 < π * |x| := by
    have : 0 < |x| := abs_pos.mpr hx
    positivity
  have hfin : (π * |x|)⁻¹ * (2 * π * |x|) = 2 := by field_simp
  rw [norm_div, hden, div_le_iff₀ (by positivity)]
  exact le_of_le_of_eq hnum hfin.symm

/-- The sampling kernel: the transform of the trapezoidal cutoff. -/
def sampKernel (a : ℝ) : ℝ → ℂ := 𝓕 (trapFn a)

theorem sampKernel_eq (a x : ℝ) :
    sampKernel a x = ((2 * a)⁻¹ : ℂ) * (𝓕 (boxFn a) x * 𝓕 (boxFn (2 * a)) x) := by
  have hconv := Real.fourier_bilin_convolution_eq (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_boxFn a) (integrable_boxFn (2 * a)) x
  have hsmul : 𝓕 (trapFn a) x = ((2 * a)⁻¹ : ℂ) *
      𝓕 (convolution (boxFn a) (boxFn (2 * a)) (ContinuousLinearMap.mul ℂ ℂ) volume) x := by
    simp_rw [Real.fourier_eq', trapFn, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with t
    ring
  rw [sampKernel, hsmul, hconv]
  rfl

/-- **Quadratic decay of the kernel.** -/
theorem norm_sampKernel_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖sampKernel a x‖ ≤ (8 * a + a⁻¹) / (1 + x ^ 2) := by
  have ha' : (0:ℝ) < 2 * a := by linarith
  rw [sampKernel_eq, norm_mul, norm_mul]
  have hc : ‖((2 * a)⁻¹ : ℂ)‖ = (2 * a)⁻¹ := by
    rw [show ((2 * a)⁻¹ : ℂ) = (((2 * a)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  have hden : (0:ℝ) < 1 + x ^ 2 := by positivity
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 : ‖𝓕 (boxFn a) x‖ ≤ 2 * a := norm_fourier_boxFn_le_two_mul ha.le x
    have h2 : ‖𝓕 (boxFn (2 * a)) x‖ ≤ 2 * (2 * a) := norm_fourier_boxFn_le_two_mul ha'.le x
    have hx2 : x ^ 2 ≤ 1 := by
      have := abs_nonneg x
      nlinarith [sq_abs x]
    have hstep : (2 * a)⁻¹ * (‖𝓕 (boxFn a) x‖ * ‖𝓕 (boxFn (2 * a)) x‖) ≤ 4 * a := by
      have hmul : ‖𝓕 (boxFn a) x‖ * ‖𝓕 (boxFn (2 * a)) x‖ ≤ (2 * a) * (2 * (2 * a)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc (2 * a)⁻¹ * (‖𝓕 (boxFn a) x‖ * ‖𝓕 (boxFn (2 * a)) x‖)
          ≤ (2 * a)⁻¹ * ((2 * a) * (2 * (2 * a))) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = 4 * a := by field_simp; ring
    refine hstep.trans ?_
    rw [le_div_iff₀ hden]
    nlinarith [ha.le, hx2, inv_pos.mpr ha]
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx
      norm_num at hx
    have h1 : ‖𝓕 (boxFn a) x‖ ≤ (π * |x|)⁻¹ := norm_fourier_boxFn_le_inv ha.le hx0
    have h2 : ‖𝓕 (boxFn (2 * a)) x‖ ≤ (π * |x|)⁻¹ := norm_fourier_boxFn_le_inv ha'.le hx0
    have hπx : 0 < π * |x| := by
      have : (0:ℝ) < |x| := by linarith
      positivity
    have hstep : (2 * a)⁻¹ * (‖𝓕 (boxFn a) x‖ * ‖𝓕 (boxFn (2 * a)) x‖) ≤
        (2 * a)⁻¹ * ((π * |x|)⁻¹ * (π * |x|)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by positivity)
    refine hstep.trans ?_
    rw [le_div_iff₀ hden]
    have hpi : (1:ℝ) ≤ π := by linarith [Real.pi_gt_three]
    have hxx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have hx1 : (1:ℝ) < |x| := hx
    have hkey : (2 * a)⁻¹ * ((π * |x|)⁻¹ * (π * |x|)⁻¹) * (1 + x ^ 2) ≤ a⁻¹ := by
      rw [hxx]
      have hfac : (π * |x|)⁻¹ * (π * |x|)⁻¹ = (π ^ 2)⁻¹ * (|x| ^ 2)⁻¹ := by
        field_simp
      rw [hfac]
      have hone : (1:ℝ) + |x| ^ 2 ≤ 2 * |x| ^ 2 := by nlinarith
      have hpos : (0:ℝ) < |x| ^ 2 := by positivity
      have hstep2 : (2 * a)⁻¹ * ((π ^ 2)⁻¹ * (|x| ^ 2)⁻¹) * (1 + |x| ^ 2) ≤
          (2 * a)⁻¹ * ((π ^ 2)⁻¹ * (|x| ^ 2)⁻¹) * (2 * |x| ^ 2) := by
        apply mul_le_mul_of_nonneg_left hone (by positivity)
      refine hstep2.trans ?_
      have : (2 * a)⁻¹ * ((π ^ 2)⁻¹ * (|x| ^ 2)⁻¹) * (2 * |x| ^ 2) = a⁻¹ * (π ^ 2)⁻¹ := by
        field_simp
      rw [this]
      have hπ2 : (1:ℝ) ≤ π ^ 2 := by nlinarith
      have : a⁻¹ * (π ^ 2)⁻¹ ≤ a⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [inv_le_one₀ (by positivity)]
        exact hπ2
      linarith [this]
    nlinarith [hkey, ha, inv_pos.mpr ha]

theorem integrable_sampKernel {a : ℝ} (ha : 0 < a) : Integrable (sampKernel a) := by
  have hdom : Integrable (fun x : ℝ => (8 * a + a⁻¹) / (1 + x ^ 2)) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (integrable_inv_one_add_sq.const_mul (8 * a + a⁻¹))
  refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) (integrable_trapFn ha)).aestronglyMeasurable
  · exact norm_sampKernel_le ha x

/-! ## The reproducing identity -/

theorem fourierInv_sampKernel {a : ℝ} (ha : 0 < a) : 𝓕⁻ (sampKernel a) = trapFn a := by
  show 𝓕⁻ (𝓕 (trapFn a)) = trapFn a
  exact (continuous_trapFn a).fourierInv_fourier_eq (integrable_trapFn ha)
    (integrable_sampKernel ha)

private theorem fourier_shift_sampKernel {a : ℝ} (ha : 0 < a) (x₀ x : ℝ) :
    𝓕 (fun ξ : ℝ => sampKernel a (x₀ - ξ)) x =
      Complex.exp (((-2 * π * x₀ * x : ℝ) : ℂ) * Complex.I) * trapFn a x := by
  set F : ℝ → ℂ := fun u =>
    Complex.exp (((-2 * π * (x₀ - u) * x : ℝ) : ℂ) * Complex.I) * sampKernel a u with hF
  have hstep1 : 𝓕 (fun ξ : ℝ => sampKernel a (x₀ - ξ)) x = ∫ ξ : ℝ, F (x₀ - ξ) := by
    rw [Real.fourier_eq']
    congr 1 with ξ
    have hin : (inner ℝ ξ x : ℝ) = ξ * x := by simp [RCLike.inner_apply, mul_comm]
    have harg : (-2 * π * (inner ℝ ξ x : ℝ) : ℝ) = -2 * π * (x₀ - (x₀ - ξ)) * x := by
      rw [hin]
      try ring
    simp only [hF, smul_eq_mul, harg]
  have hstep2 : (∫ ξ : ℝ, F (x₀ - ξ)) = ∫ u : ℝ, F u := integral_sub_left_eq_self F volume x₀
  have hstep3 : (∫ u : ℝ, F u) =
      Complex.exp (((-2 * π * x₀ * x : ℝ) : ℂ) * Complex.I) *
        ∫ u : ℝ, Complex.exp (((2 * π * u * x : ℝ) : ℂ) * Complex.I) * sampKernel a u := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with u
    simp only [hF]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hstep4 : (∫ u : ℝ, Complex.exp (((2 * π * u * x : ℝ) : ℂ) * Complex.I) *
      sampKernel a u) = trapFn a x := by
    have hinv : 𝓕⁻ (sampKernel a) x = trapFn a x := by rw [fourierInv_sampKernel ha]
    rw [← hinv, Real.fourierInv_eq']
    congr 1 with u
    have hin : (inner ℝ u x : ℝ) = u * x := by simp [RCLike.inner_apply, mul_comm]
    have harg : (2 * π * (inner ℝ u x : ℝ) : ℝ) = 2 * π * u * x := by
      rw [hin]
      try ring
    simp only [smul_eq_mul, harg]
  rw [hstep1, hstep2, hstep3, hstep4]

/-- **The reproducing identity.**  A transform of a source supported in `[−a, a]` is its own
convolution against the kernel. -/
theorem fourier_eq_integral_mul_sampKernel {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : Integrable f) (hsupp : ∀ t : ℝ, a < |t| → f t = 0) (x₀ : ℝ) :
    𝓕 f x₀ = ∫ x : ℝ, 𝓕 f x * sampKernel a (x₀ - x) := by
  have hg : Integrable (fun ξ : ℝ => sampKernel a (x₀ - ξ)) :=
    (integrable_sampKernel ha).comp_sub_left x₀
  have hLflip : (LinearMap.flip (innerₗ ℝ)) = innerₗ ℝ := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    simp [mul_comm]
  have hcont : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 := continuous_inner
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := 𝐞) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := f) (g := fun ξ : ℝ => sampKernel a (x₀ - ξ)) Real.continuous_fourierChar hcont hf hg
  rw [hLflip] at hflip
  have hleft : (∫ ξ : ℝ, 𝓕 f ξ • sampKernel a (x₀ - ξ)) =
      ∫ x : ℝ, 𝓕 f x * sampKernel a (x₀ - x) := by
    simp only [smul_eq_mul]
  have hexpeq : ∀ x : ℝ, Complex.exp (((-2 * π * (inner ℝ x x₀ : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-2 * π * x₀ * x : ℝ) : ℂ) * Complex.I) := by
    intro x
    have hin : (inner ℝ x x₀ : ℝ) = x * x₀ := by simp [RCLike.inner_apply, mul_comm]
    have harg : (-2 * π * (inner ℝ x x₀ : ℝ) : ℝ) = -2 * π * x₀ * x := by
      rw [hin]
      try ring
    rw [harg]
  have hright : (∫ x : ℝ, f x • 𝓕 (fun ξ : ℝ => sampKernel a (x₀ - ξ)) x) = 𝓕 f x₀ := by
    rw [Real.fourier_eq' f x₀]
    congr 1 with x
    simp only [smul_eq_mul]
    rw [fourier_shift_sampKernel ha, hexpeq x]
    by_cases hx : |x| ≤ a
    · rw [trapFn_eq_one ha hx, mul_one, mul_comm]
    · rw [hsupp x (not_le.mp hx), zero_mul, mul_zero]
  rw [← hleft, ← hright]
  exact hflip.symm

/-! ## The localised sampling bound -/

theorem continuous_sampKernel {a : ℝ} (ha : 0 < a) : Continuous (sampKernel a) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by exact continuous_inner) (integrable_trapFn ha)

/-- The kernel's mass, with the explicit bound `(8a + a⁻¹)π`. -/
theorem integral_norm_sampKernel_le {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, ‖sampKernel a x‖ ≤ (8 * a + a⁻¹) * π := by
  have hdom : Integrable (fun x : ℝ => (8 * a + a⁻¹) / (1 + x ^ 2)) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (integrable_inv_one_add_sq.const_mul (8 * a + a⁻¹))
  have hmono : (∫ x : ℝ, ‖sampKernel a x‖) ≤ ∫ x : ℝ, (8 * a + a⁻¹) / (1 + x ^ 2) :=
    integral_mono (integrable_sampKernel ha).norm hdom (fun x => norm_sampKernel_le ha x)
  refine hmono.trans (le_of_eq ?_)
  have : (∫ x : ℝ, (8 * a + a⁻¹) / (1 + x ^ 2)) = (8 * a + a⁻¹) * ∫ x : ℝ, (1 + x ^ 2)⁻¹ := by
    simp_rw [div_eq_mul_inv]
    exact MeasureTheory.integral_const_mul _ _
  rw [this, integral_univ_inv_one_add_sq]

/-- **Localised sampling bound.**  The pointwise square of a transform of a source supported in
`[−a, a]` is controlled by its square averaged against a kernel of quadratic decay. -/
theorem norm_sq_fourier_le_integral {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : Integrable f) (hsupp : ∀ t : ℝ, a < |t| → f t = 0) (x₀ : ℝ)
    (hsq : Integrable fun x : ℝ => ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖ ^ 2) :
    ‖𝓕 f x₀‖ ^ 2 ≤ ((8 * a + a⁻¹) * π) *
      ∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖ ^ 2 := by
  have hGc : Continuous fun x : ℝ => sampKernel a (x₀ - x) :=
    (continuous_sampKernel ha).comp (continuous_const.sub continuous_id)
  have hΦc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hwi : Integrable fun x : ℝ => ‖sampKernel a (x₀ - x)‖ :=
    ((integrable_sampKernel ha).comp_sub_left x₀).norm
  have h1 : ‖𝓕 f x₀‖ ≤ ∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖ := by
    rw [fourier_eq_integral_mul_sampKernel ha hf hsupp x₀]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1 with x
    rw [norm_mul]
    ring
  have h2 := sq_integral_weighted_le (μ := (volume : Measure ℝ))
    (w := fun x : ℝ => ‖sampKernel a (x₀ - x)‖) (g := fun x : ℝ => ‖𝓕 f x‖)
    (fun y => norm_nonneg _) hGc.norm.aestronglyMeasurable
    hΦc.norm.aestronglyMeasurable hwi hsq
  have h3 : (∫ x : ℝ, ‖sampKernel a (x₀ - x)‖) ≤ (8 * a + a⁻¹) * π := by
    have hsub : (∫ x : ℝ, ‖sampKernel a (x₀ - x)‖) = ∫ x : ℝ, ‖sampKernel a x‖ :=
      integral_sub_left_eq_self (fun u : ℝ => ‖sampKernel a u‖) volume x₀
    rw [hsub]
    exact integral_norm_sampKernel_le ha
  have hwg2 : 0 ≤ ∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖ ^ 2 :=
    integral_nonneg fun x => by positivity
  have h4 : ‖𝓕 f x₀‖ ^ 2 ≤ (∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h1
  calc ‖𝓕 f x₀‖ ^ 2 ≤ (∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖) ^ 2 := h4
    _ ≤ (∫ x : ℝ, ‖sampKernel a (x₀ - x)‖) *
          ∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖ ^ 2 := h2
    _ ≤ ((8 * a + a⁻¹) * π) * ∫ x : ℝ, ‖sampKernel a (x₀ - x)‖ * ‖𝓕 f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 hwg2

end

end GaloisForLFunctions.HTGeometry.LocalSampling
