import GaloisForLFunctions.RHTower.StripHorizontalShift
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Hardy transfer for even real sources on a strip

Let `T` be holomorphic on the strip `|Im z| < c₀`, even, real on the real line, and exponentially
decaying in the real direction on every closed substrip.  Its Fourier transform `ρ = 𝓕 T|ℝ` is then
real, even, continuous, and decays at every rate below `2πc₀`; inversion on each horizontal line gives
`T(a + iy) = ∫ e(wa) e^{-2πyw} ρ(w) dw`, and on the imaginary axis `T(iy) = ∫ cosh(2πyw) ρ(w) dw`.

**Transfer.**  If `ρ` keeps one sign on `|w| ≥ W` and `T` is bounded on the imaginary axis, Fatou's
lemma turns the axis bound into the exponential moment `∫ e^{2πc₀|w|} |ρ(w)| dw < ∞`, and then `T`
is bounded on the whole open strip.  Contrapositively, if `T` is bounded on the imaginary axis but
unbounded on the strip, then `ρ` has zeros beyond every height.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace RHTower

noncomputable section

section StripHardy

variable {T : ℂ → ℂ} {c₀ : ℝ}

theorem fourier_real_eq_integral_exp (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (-(2 * π * I * v * w)) * f v := by
  rw [Real.fourier_real_eq]
  refine integral_congr_ae ?_
  filter_upwards with v
  show (Real.fourierChar (-(v * w))) • f v = Complex.exp (-(2 * π * I * v * w)) * f v
  rw [Circle.smul_def]
  congr 1
  rw [Real.fourierChar_apply]
  push_cast
  ring_nf

theorem strip_point_im (a y : ℝ) : ((a : ℂ) + (y : ℂ) * I).im = y := by simp

theorem strip_point_re (a y : ℝ) : ((a : ℂ) + (y : ℂ) * I).re = a := by simp

theorem continuous_strip_line (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z) {y : ℝ}
    (hy : |y| < c₀) : Continuous (fun a : ℝ => T ((a : ℂ) + (y : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmem : |((a : ℂ) + (y : ℂ) * I).im| < c₀ := by rw [strip_point_im]; exact hy
  exact ContinuousAt.comp (g := T) (f := fun t : ℝ => (t : ℂ) + (y : ℂ) * I) (x := a)
    (hholo _ hmem).continuousAt (by fun_prop)

theorem continuous_strip_real (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hc₀ : 0 < c₀) : Continuous (fun a : ℝ => T (a : ℂ)) := by
  have h := continuous_strip_line hholo (y := 0) (by simpa using hc₀)
  simpa using h

theorem integrable_strip_line (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    {β y : ℝ} (hβ0 : 0 ≤ β) (hβ : β < c₀) (hy : |y| ≤ β) :
    Integrable (fun a : ℝ => T ((a : ℂ) + (y : ℂ) * I)) := by
  obtain ⟨C, _, hC⟩ := hdec β hβ0 hβ
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' one_pos).const_mul C)
    (continuous_strip_line hholo (lt_of_le_of_lt hy hβ)).aestronglyMeasurable ?_
  filter_upwards with a
  have h := hC ((a : ℂ) + (y : ℂ) * I) (by rw [strip_point_im]; exact hy)
  rw [strip_point_re] at h
  simpa using h

theorem integrable_strip_real (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (hc₀ : 0 < c₀) : Integrable (fun a : ℝ => T (a : ℂ)) := by
  have h := integrable_strip_line hholo hdec (β := 0) (y := 0) le_rfl hc₀ (by simp)
  simpa using h

/-- **Contour shift for the Fourier transform.** -/
theorem fourier_strip_line (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < c₀) (w : ℝ) :
    𝓕 (fun a : ℝ => T ((a : ℂ) + (y : ℂ) * I)) w =
      (Real.exp (-(2 * π * y * w)) : ℂ) * 𝓕 (fun a : ℝ => T (a : ℂ)) w := by
  obtain ⟨C, hC0, hC⟩ := hdec y hy0 hy
  set H : ℂ → ℂ := fun z => cexp (-(2 * π * I * z * (w : ℂ))) * T z with hH
  have hdiff : ∀ z : ℂ, |z.im| ≤ y → DifferentiableAt ℂ H z := by
    intro z hz
    refine DifferentiableAt.mul ?_ (hholo z (lt_of_le_of_lt hz hy))
    exact (differentiable_exp.differentiableAt).comp z (by fun_prop)
  have hnormexp : ∀ z : ℂ, ‖cexp (-(2 * π * I * z * (w : ℂ)))‖ = Real.exp (2 * π * w * z.im) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hbound : ∀ z : ℂ, |z.im| ≤ y →
      ‖H z‖ ≤ (C * Real.exp (2 * π * |w| * y)) * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    rw [hH]
    simp only
    rw [norm_mul, hnormexp]
    have hsrc := hC z hz
    have hexpmono : Real.exp (2 * π * w * z.im) ≤ Real.exp (2 * π * |w| * y) := by
      rw [Real.exp_le_exp]
      have h1 : w * z.im ≤ |w * z.im| := le_abs_self _
      have h2 : |w * z.im| = |w| * |z.im| := abs_mul w z.im
      have h3 : |w| * |z.im| ≤ |w| * y := mul_le_mul_of_nonneg_left hz (abs_nonneg w)
      have h4 : (0 : ℝ) < 2 * π := by positivity
      nlinarith [h1, h2, h3]
    calc Real.exp (2 * π * w * z.im) * ‖T z‖
        ≤ Real.exp (2 * π * |w| * y) * (C * Real.exp (-|z.re|)) :=
          mul_le_mul hexpmono hsrc (norm_nonneg _) (Real.exp_pos _).le
      _ = (C * Real.exp (2 * π * |w| * y)) * Real.exp (-(1 * |z.re|)) := by
          rw [one_mul]; ring
  have hshift := integral_horizontal_shift_of_decay (F := H) (c := y)
    (C := C * Real.exp (2 * π * |w| * y)) (r := 1) hy0 one_pos hdiff hbound
  have hline : ∀ a : ℝ, H ((a : ℂ) + (y : ℂ) * I)
      = cexp ((2 * π * y * w : ℝ) : ℂ) * (cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) *
        T ((a : ℂ) + (y : ℂ) * I)) := by
    intro a
    have hexp : -(2 * π * I * ((a : ℂ) + (y : ℂ) * I) * (w : ℂ))
        = ((2 * π * y * w : ℝ) : ℂ) + -(2 * π * I * (a : ℂ) * (w : ℂ)) := by
      push_cast
      linear_combination (-(2 * (π : ℂ) * (y : ℂ) * (w : ℂ))) * Complex.I_sq
    rw [hH]
    simp only
    rw [hexp, Complex.exp_add, mul_assoc]
  have hfourierline := fourier_real_eq_integral_exp (fun a : ℝ => T ((a : ℂ) + (y : ℂ) * I)) w
  have hfourierbase : 𝓕 (fun a : ℝ => T (a : ℂ)) w = ∫ a : ℝ, H (a : ℂ) := by
    rw [fourier_real_eq_integral_exp]
  have hleft : (∫ a : ℝ, H ((a : ℂ) + (y : ℂ) * I))
      = cexp ((2 * π * y * w : ℝ) : ℂ) *
        ∫ a : ℝ, cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) * T ((a : ℂ) + (y : ℂ) * I) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards with a; exact hline a)
  rw [hleft, hfourierbase.symm] at hshift
  rw [hfourierline, ← hshift]
  have hcancel : ((Real.exp (-(2 * π * y * w)) : ℝ) : ℂ) * cexp (((2 * π * y * w : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  rw [← mul_assoc, hcancel, one_mul]

/-- The Fourier transform of an even function is even. -/
theorem fourier_even_of_even {f : ℝ → ℂ} (hf : ∀ a : ℝ, f (-a) = f a) (w : ℝ) :
    𝓕 f (-w) = 𝓕 f w := by
  rw [fourier_real_eq_integral_exp, fourier_real_eq_integral_exp]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae ?_
  filter_upwards with v
  rw [hf v]
  congr 2
  push_cast
  ring

/-- The Fourier transform of an even real function is real. -/
theorem fourier_im_eq_zero_of_even_real {f : ℝ → ℂ} (hf : ∀ a : ℝ, f (-a) = f a)
    (hr : ∀ a : ℝ, (f a).im = 0) (w : ℝ) : (𝓕 f w).im = 0 := by
  have hconj : (starRingEnd ℂ) (𝓕 f w) = 𝓕 f (-w) := by
    rw [fourier_real_eq_integral_exp, fourier_real_eq_integral_exp, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards with v
    rw [map_mul, ← Complex.exp_conj]
    have hfr : (starRingEnd ℂ) (f v) = f v := Complex.conj_eq_iff_im.mpr (hr v)
    rw [hfr]
    congr 2
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  rw [fourier_even_of_even hf] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

/-- **Decay of the Fourier transform.** -/
theorem norm_fourier_strip_le (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < c₀) (w : ℝ) :
    ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖ ≤
      (∫ a : ℝ, ‖T ((a : ℂ) + (β : ℂ) * I)‖) * Real.exp (-(2 * π * β * |w|)) := by
  have hev : ∀ a : ℝ, (fun a : ℝ => T (a : ℂ)) (-a) = (fun a : ℝ => T (a : ℂ)) a := by
    intro a; simp only [Complex.ofReal_neg]; exact heven a
  have hneg : ∀ w : ℝ, w ≤ 0 → ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖ ≤
      (∫ a : ℝ, ‖T ((a : ℂ) + (β : ℂ) * I)‖) * Real.exp (-(2 * π * β * |w|)) := by
    intro w hw
    have h := fourier_strip_line hholo hdec hβ0 hβ w
    have hne : ((Real.exp (-(2 * π * β * w)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    have heq : 𝓕 (fun a : ℝ => T (a : ℂ)) w =
        ((Real.exp (2 * π * β * w) : ℝ) : ℂ) * 𝓕 (fun a : ℝ => T ((a : ℂ) + (β : ℂ) * I)) w := by
      rw [h, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    have hb : ‖𝓕 (fun a : ℝ => T ((a : ℂ) + (β : ℂ) * I)) w‖ ≤
        ∫ a : ℝ, ‖T ((a : ℂ) + (β : ℂ) * I)‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have he : Real.exp (2 * π * β * w) = Real.exp (-(2 * π * β * |w|)) := by
      rw [abs_of_nonpos hw]; ring_nf
    rw [he]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  rcases le_total w 0 with hw | hw
  · exact hneg w hw
  · have h := hneg (-w) (by linarith)
    rw [fourier_even_of_even hev, abs_neg] at h
    exact h

theorem integrable_exp_mul_norm_fourier_strip
    (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) {y : ℝ} (hy0 : 0 ≤ y) (hy : y < c₀) :
    Integrable (fun w : ℝ => Real.exp (2 * π * y * |w|) * ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖) := by
  set β : ℝ := (y + c₀) / 2 with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  have hβ : β < c₀ := by rw [hβdef]; linarith
  have hyβ : y < β := by rw [hβdef]; linarith
  set K : ℝ := ∫ a : ℝ, ‖T ((a : ℂ) + (β : ℂ) * I)‖ with hK
  have hc₀ : 0 < c₀ := lt_of_le_of_lt hy0 hy
  have hcont : Continuous (𝓕 (fun a : ℝ => T (a : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      (integrable_strip_real hholo hdec hc₀)
  have hrate : 0 < 2 * π * (β - y) := by
    have := Real.pi_pos; have : 0 < β - y := by linarith
    positivity
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' hrate).const_mul K) ?_ ?_
  · exact ((by fun_prop : Continuous fun w : ℝ => Real.exp (2 * π * y * |w|)).mul
      hcont.norm).aestronglyMeasurable
  · filter_upwards with w
    rw [Real.norm_of_nonneg (by positivity)]
    have h := norm_fourier_strip_le hholo hdec heven hβ0 hβ w
    calc Real.exp (2 * π * y * |w|) * ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖
        ≤ Real.exp (2 * π * y * |w|) * (K * Real.exp (-(2 * π * β * |w|))) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = K * Real.exp (-(2 * π * (β - y) * |w|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- **Fourier inversion on the horizontal lines of the strip.** -/
theorem strip_line_eq_integral (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) {y : ℝ} (hy0 : 0 ≤ y) (hy : y < c₀) (a : ℝ) :
    T ((a : ℂ) + (y : ℂ) * I)
      = ∫ w : ℝ, (Real.fourierChar (w * a)) •
          ((Real.exp (-(2 * π * y * w)) : ℂ) * 𝓕 (fun a : ℝ => T (a : ℂ)) w) := by
  set g : ℝ → ℂ := fun a => T ((a : ℂ) + (y : ℂ) * I) with hg
  have hgint : Integrable g :=
    integrable_strip_line hholo hdec (β := y) hy0 hy (by rw [abs_of_nonneg hy0])
  have hfint : Integrable (𝓕 g) := by
    have hbound := integrable_exp_mul_norm_fourier_strip hholo hdec heven hy0 hy
    have hc₀ : 0 < c₀ := lt_of_le_of_lt hy0 hy
    have hcont : Continuous (𝓕 (fun a : ℝ => T (a : ℂ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
        (integrable_strip_real hholo hdec hc₀)
    refine Integrable.mono' hbound ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by
        refine Continuous.mul ?_ hcont
        exact Complex.continuous_ofReal.comp (by fun_prop))).congr
        (Filter.Eventually.of_forall (fun w => (fourier_strip_line hholo hdec hy0 hy w).symm))
    · filter_upwards with w
      rw [fourier_strip_line hholo hdec hy0 hy w, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.exp_le_exp]
      have h1 : -(w) ≤ |w| := neg_le_abs w
      have h2 : (0 : ℝ) ≤ 2 * π * y := by
        have := Real.pi_pos
        positivity
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      nlinarith [h3]
  have hcont : ∀ b : ℝ, ContinuousAt g b := fun b =>
    (continuous_strip_line hholo (by rw [abs_of_nonneg hy0]; exact hy)).continuousAt
  have hinv := hgint.fourierInv_fourier_eq hfint (hcont a)
  rw [Real.fourierInv_eq] at hinv
  have hga : g a = T ((a : ℂ) + (y : ℂ) * I) := rfl
  rw [hga] at hinv
  rw [← hinv]
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [fourier_strip_line hholo hdec hy0 hy w]
  congr 2
  simp [RCLike.inner_apply, mul_comm]

/-- The inversion integral bounds the source on every horizontal line of the upper half strip. -/
theorem norm_strip_line_le (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) {y : ℝ} (hy0 : 0 ≤ y) (hy : y < c₀) (a : ℝ) :
    ‖T ((a : ℂ) + (y : ℂ) * I)‖
      ≤ ∫ w : ℝ, Real.exp (-(2 * π * y * w)) * ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖ := by
  rw [strip_line_eq_integral hholo hdec heven hy0 hy a]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [Circle.norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-! ## The real density and its cosh moments -/

/-- The real Fourier density. -/
def stripDensity (T : ℂ → ℂ) (w : ℝ) : ℝ := (𝓕 (fun a : ℝ => T (a : ℂ)) w).re

theorem fourier_eq_stripDensity (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ))
    (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0) (w : ℝ) :
    𝓕 (fun a : ℝ => T (a : ℂ)) w = (stripDensity T w : ℂ) := by
  have hev : ∀ a : ℝ, (fun a : ℝ => T (a : ℂ)) (-a) = (fun a : ℝ => T (a : ℂ)) a := by
    intro a; simp only [Complex.ofReal_neg]; exact heven a
  have him := fourier_im_eq_zero_of_even_real hev hreal w
  apply Complex.ext <;> simp [stripDensity, him]

theorem stripDensity_neg (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) (w : ℝ) :
    stripDensity T (-w) = stripDensity T w := by
  have hev : ∀ a : ℝ, (fun a : ℝ => T (a : ℂ)) (-a) = (fun a : ℝ => T (a : ℂ)) a := by
    intro a; simp only [Complex.ofReal_neg]; exact heven a
  unfold stripDensity; rw [fourier_even_of_even hev]

theorem continuous_stripDensity (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (hc₀ : 0 < c₀) : Continuous (stripDensity T) :=
  Complex.continuous_re.comp (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) (integrable_strip_real hholo hdec hc₀))

theorem integrable_exp_mul_stripDensity (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0)
    {y : ℝ} (hy : |y| < c₀) :
    Integrable (fun w : ℝ => Real.exp (-(2 * π * y * w)) * stripDensity T w) := by
  have hc₀ : 0 < c₀ := lt_of_le_of_lt (abs_nonneg y) hy
  have hbound := integrable_exp_mul_norm_fourier_strip hholo hdec heven (abs_nonneg y) hy
  refine Integrable.mono' hbound ?_ ?_
  · exact ((by fun_prop : Continuous fun w : ℝ => Real.exp (-(2 * π * y * w))).mul
      (continuous_stripDensity hholo hdec hc₀)).aestronglyMeasurable
  · filter_upwards with w
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), fourier_eq_stripDensity heven hreal,
      Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp]
    have h1 : -(y * w) ≤ |y * w| := neg_le_abs _
    have h2 : |y * w| = |y| * |w| := abs_mul y w
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * π)
    have h4 : -(2 * π * y * w) = 2 * π * -(y * w) := by ring
    have h5 : 2 * π * |y| * |w| = 2 * π * |y * w| := by rw [h2]; ring
    linarith

theorem strip_axis_eq_ofReal (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0)
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y < c₀) :
    T ((y : ℂ) * I) = ((∫ w : ℝ, Real.exp (-(2 * π * y * w)) * stripDensity T w : ℝ) : ℂ) := by
  have h := strip_line_eq_integral hholo hdec heven hy0 hy 0
  rw [show ((0 : ℝ) : ℂ) + (y : ℂ) * I = (y : ℂ) * I by norm_num] at h
  rw [h, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [show w * (0 : ℝ) = 0 by ring, fourier_eq_stripDensity heven hreal]
  simp

theorem integral_cosh_stripDensity (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0)
    {y : ℝ} (hy : |y| < c₀) :
    (∫ w : ℝ, Real.exp (-(2 * π * y * w)) * stripDensity T w)
      = ∫ w : ℝ, Real.cosh (2 * π * y * w) * stripDensity T w := by
  have h1 := integrable_exp_mul_stripDensity hholo hdec heven hreal hy
  have h2 : Integrable (fun w : ℝ => Real.exp (2 * π * y * w) * stripDensity T w) := by
    have h := integrable_exp_mul_stripDensity hholo hdec heven hreal (y := -y) (by rwa [abs_neg])
    refine h.congr ?_
    filter_upwards with w
    congr 2
    ring
  have hsym : (∫ w : ℝ, Real.exp (-(2 * π * y * w)) * stripDensity T w)
      = ∫ w : ℝ, Real.exp (2 * π * y * w) * stripDensity T w := by
    have h := integral_neg_eq_self
      (fun w : ℝ => Real.exp (2 * π * y * w) * stripDensity T w) volume
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards with w
    rw [stripDensity_neg heven]
    congr 2
    ring
  have hpoint : ∀ w : ℝ, Real.cosh (2 * π * y * w) * stripDensity T w
      = (Real.exp (-(2 * π * y * w)) * stripDensity T w
        + Real.exp (2 * π * y * w) * stripDensity T w) / 2 := by
    intro w
    rw [Real.cosh_eq]
    ring
  rw [show (∫ w : ℝ, Real.cosh (2 * π * y * w) * stripDensity T w)
      = ∫ w : ℝ, (Real.exp (-(2 * π * y * w)) * stripDensity T w
        + Real.exp (2 * π * y * w) * stripDensity T w) / 2 from
    integral_congr_ae (by filter_upwards with w using hpoint w)]
  rw [integral_div, integral_add h1 h2, ← hsym]
  ring

/-! ## One-signed tails and the exponential moment -/

/-- **Axis bound and a one-signed tail give the full exponential moment.** -/
theorem integrable_exp_mul_abs_stripDensity
    (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ)) (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0)
    (hc₀ : 0 < c₀) {B₁ : ℝ} (hax : ∀ y : ℝ, 0 ≤ y → y < c₀ → ‖T ((y : ℂ) * I)‖ ≤ B₁)
    {W σ : ℝ} (hW : 0 < W) (hσ : |σ| = 1)
    (hsign : ∀ w : ℝ, W ≤ |w| → 0 ≤ σ * stripDensity T w) :
    Integrable (fun w : ℝ => Real.exp (2 * π * c₀ * |w|) * |stripDensity T w|) := by
  have hpi := Real.pi_pos
  have hρc := continuous_stripDensity hholo hdec hc₀
  set S : Set ℝ := {w : ℝ | W ≤ |w|} with hS
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hmidsub : Sᶜ ⊆ Set.Icc (-W) W := by
    intro w hw
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
    exact ⟨by linarith [neg_abs_le w], by linarith [le_abs_self w]⟩
  have hmidint : IntegrableOn (fun w : ℝ => |stripDensity T w|) Sᶜ :=
    IntegrableOn.mono_set (hρc.abs.integrableOn_Icc) hmidsub
  set B₀ : ℝ := Real.cosh (2 * π * c₀ * W) * ∫ w in Sᶜ, |stripDensity T w| with hB₀def
  have hintnn : (0 : ℝ) ≤ ∫ w in Sᶜ, |stripDensity T w| :=
    integral_nonneg_of_ae (by filter_upwards with w using abs_nonneg _)
  have hcoshint : ∀ y : ℝ, |y| < c₀ →
      Integrable (fun w : ℝ => Real.cosh (2 * π * y * w) * (σ * stripDensity T w)) := by
    intro y hy
    have h1 := integrable_exp_mul_stripDensity hholo hdec heven hreal hy
    have h2 : Integrable (fun w : ℝ => Real.exp (2 * π * y * w) * stripDensity T w) := by
      have h := integrable_exp_mul_stripDensity hholo hdec heven hreal (y := -y) (by rwa [abs_neg])
      refine h.congr ?_
      filter_upwards with w
      congr 2
      ring
    refine (((h1.add h2).div_const 2).const_mul σ).congr ?_
    filter_upwards with w
    simp only [Pi.add_apply]
    rw [Real.cosh_eq]
    ring
  have hmidbound : ∀ y : ℝ, 0 ≤ y → y < c₀ →
      |∫ w in Sᶜ, Real.cosh (2 * π * y * w) * (σ * stripDensity T w)| ≤ B₀ := by
    intro y hy0 hy
    have habs : |y| < c₀ := by rwa [abs_of_nonneg hy0]
    have hint := (hcoshint y habs).restrict (s := Sᶜ)
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hB₀def, ← integral_const_mul]
    refine integral_mono_ae hint.abs (hmidint.const_mul _) ?_
    filter_upwards [ae_restrict_mem hSmeas.compl] with w hw
    show |Real.cosh (2 * π * y * w) * (σ * stripDensity T w)|
      ≤ Real.cosh (2 * π * c₀ * W) * |stripDensity T w|
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
    rw [abs_mul, abs_mul, hσ, one_mul, abs_of_pos (Real.cosh_pos _)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * c₀ * W)]
    rw [show |2 * π * y * w| = 2 * π * y * |w| by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * y)]]
    have hyw : y * |w| ≤ c₀ * W :=
      mul_le_mul hy.le hw.le (abs_nonneg w) hc₀.le
    nlinarith [mul_le_mul_of_nonneg_left hyw (by positivity : (0:ℝ) ≤ 2 * π)]
  set B : ℝ := B₁ + B₀ with hBdef
  have htail : ∀ y : ℝ, 0 ≤ y → y < c₀ →
      (∫ w in S, Real.cosh (2 * π * y * w) * (σ * stripDensity T w)) ≤ B := by
    intro y hy0 hy
    have habs : |y| < c₀ := by rwa [abs_of_nonneg hy0]
    have hint := hcoshint y habs
    have hsplit := integral_add_compl hSmeas hint
    have hglobal : |∫ w : ℝ, Real.cosh (2 * π * y * w) * (σ * stripDensity T w)| ≤ B₁ := by
      have hpull : (∫ w : ℝ, Real.cosh (2 * π * y * w) * (σ * stripDensity T w))
          = σ * ∫ w : ℝ, Real.cosh (2 * π * y * w) * stripDensity T w := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards with w
        ring
      rw [hpull, abs_mul, hσ, one_mul, ← integral_cosh_stripDensity hholo hdec heven hreal habs]
      have h := hax y hy0 hy
      rw [strip_axis_eq_ofReal hholo hdec heven hreal hy0 hy, Complex.norm_real,
        Real.norm_eq_abs] at h
      exact h
    have hmid := hmidbound y hy0 hy
    have h1 := abs_le.1 hglobal
    have h2 := abs_le.1 hmid
    rw [hBdef]
    linarith [hsplit, h1.2, h2.1]
  set G : ℝ → ℝ := fun w => Real.cosh (2 * π * c₀ * w) * (σ * stripDensity T w) with hGdef
  have hGcont : Continuous G :=
    (Real.continuous_cosh.comp (by fun_prop)).mul (continuous_const.mul hρc)
  have hGnn : ∀ w ∈ S, 0 ≤ G w := by
    intro w hw
    simp only [hS, Set.mem_setOf_eq] at hw
    exact mul_nonneg (Real.cosh_pos _).le (hsign w hw)
  have hfatou : ∫⁻ w in S, ENNReal.ofReal (G w) ≤ ENNReal.ofReal B := by
    set f : ℝ → ℝ → ENNReal := fun y w =>
      ENNReal.ofReal (Real.cosh (2 * π * y * w) * (σ * stripDensity T w)) with hfdef
    have hmeas : ∀ y : ℝ, Measurable (f y) := by
      intro y
      exact ENNReal.measurable_ofReal.comp
        ((Real.continuous_cosh.comp (by fun_prop)).mul (continuous_const.mul hρc)).measurable
    have hlim := lintegral_liminf_le (μ := volume.restrict S) (u := 𝓝[<] c₀) hmeas
    have hpt : ∀ w : ℝ, liminf (fun y : ℝ => f y w) (𝓝[<] c₀) = ENNReal.ofReal (G w) := by
      intro w
      refine Filter.Tendsto.liminf_eq ?_
      have hc : Continuous fun y : ℝ => Real.cosh (2 * π * y * w) * (σ * stripDensity T w) :=
        (Real.continuous_cosh.comp (by fun_prop)).mul continuous_const
      have h : Tendsto (fun y : ℝ => ENNReal.ofReal
          (Real.cosh (2 * π * y * w) * (σ * stripDensity T w))) (𝓝[<] c₀)
          (𝓝 (ENNReal.ofReal (Real.cosh (2 * π * c₀ * w) * (σ * stripDensity T w)))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((hc.tendsto c₀).mono_left nhdsWithin_le_nhds)
      rw [hGdef]
      simpa [hfdef] using h
    calc ∫⁻ w in S, ENNReal.ofReal (G w)
        = ∫⁻ w in S, liminf (fun y : ℝ => f y w) (𝓝[<] c₀) := by
          refine lintegral_congr ?_
          intro w
          rw [hpt w]
      _ ≤ liminf (fun y : ℝ => ∫⁻ w in S, f y w) (𝓝[<] c₀) := hlim
      _ ≤ ENNReal.ofReal B := by
          refine liminf_le_of_frequently_le (Filter.Eventually.frequently ?_)
          filter_upwards [Ioo_mem_nhdsLT hc₀] with y hy
          have hIntOn : IntegrableOn
              (fun w : ℝ => Real.cosh (2 * π * y * w) * (σ * stripDensity T w)) S :=
            (hcoshint y (by rw [abs_of_nonneg hy.1.le]; exact hy.2)).restrict
          have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict S]
              fun w : ℝ => Real.cosh (2 * π * y * w) * (σ * stripDensity T w) := by
            filter_upwards [ae_restrict_mem hSmeas] with w hw
            simp only [hS, Set.mem_setOf_eq] at hw
            exact mul_nonneg (Real.cosh_pos _).le (hsign w hw)
          have hofreal := ofReal_integral_eq_lintegral_ofReal hIntOn hnn
          rw [hfdef, ← hofreal]
          exact ENNReal.ofReal_le_ofReal (htail y hy.1.le hy.2)
  have hGint : IntegrableOn G S := by
    refine ⟨hGcont.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have heq : ∫⁻ w in S, ENNReal.ofReal ‖G w‖ = ∫⁻ w in S, ENNReal.ofReal (G w) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem hSmeas] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (hGnn w hw)]
    rw [heq]
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hmomcont : Continuous fun w : ℝ => Real.exp (2 * π * c₀ * |w|) * |stripDensity T w| :=
    (by fun_prop : Continuous fun w : ℝ => Real.exp (2 * π * c₀ * |w|)).mul hρc.abs
  have hSint : IntegrableOn (fun w : ℝ => Real.exp (2 * π * c₀ * |w|) * |stripDensity T w|) S := by
    refine Integrable.mono' (hGint.const_mul 2) hmomcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hSmeas] with w hw
    show ‖Real.exp (2 * π * c₀ * |w|) * |stripDensity T w|‖ ≤ 2 * G w
    simp only [hS, Set.mem_setOf_eq] at hw
    have habsval : |stripDensity T w| = σ * stripDensity T w := by
      have h1 : |σ * stripDensity T w| = σ * stripDensity T w := abs_of_nonneg (hsign w hw)
      rw [abs_mul, hσ, one_mul] at h1
      exact h1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), habsval, hGdef]
    have hexp : Real.exp (2 * π * c₀ * |w|) ≤ 2 * Real.cosh (2 * π * c₀ * w) := by
      rw [Real.cosh_eq]
      rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
      · rw [show 2 * π * c₀ * |w| = 2 * π * c₀ * w by rw [h]]
        nlinarith [Real.exp_pos (2 * π * c₀ * w), Real.exp_pos (-(2 * π * c₀ * w))]
      · rw [show 2 * π * c₀ * |w| = -(2 * π * c₀ * w) by rw [h]; ring]
        nlinarith [Real.exp_pos (2 * π * c₀ * w), Real.exp_pos (-(2 * π * c₀ * w))]
    have hnn := hsign w hw
    nlinarith [mul_le_mul_of_nonneg_right hexp hnn]
  have hScint : IntegrableOn (fun w : ℝ => Real.exp (2 * π * c₀ * |w|) * |stripDensity T w|) Sᶜ := by
    refine Integrable.mono' (hmidint.const_mul (Real.exp (2 * π * c₀ * W)))
      hmomcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hSmeas.compl] with w hw
    show ‖Real.exp (2 * π * c₀ * |w|) * |stripDensity T w|‖
      ≤ Real.exp (2 * π * c₀ * W) * |stripDensity T w|
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left hw.le (by positivity : (0:ℝ) ≤ 2 * π * c₀)
    linarith
  have hunion := hSint.union hScint
  rw [Set.union_compl_self, integrableOn_univ] at hunion
  exact hunion

/-- **Hardy transfer.**  An axis-bounded even real source whose Fourier density keeps one sign on a
tail is bounded on the whole open strip. -/
theorem strip_bounded_of_stripDensity_tail_sign
    (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (hevenC : ∀ z : ℂ, |z.im| < c₀ → T (-z) = T z) (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0)
    (hc₀ : 0 < c₀) {B₁ : ℝ} (hax : ∀ y : ℝ, 0 ≤ y → y < c₀ → ‖T ((y : ℂ) * I)‖ ≤ B₁)
    {W σ : ℝ} (hW : 0 < W) (hσ : |σ| = 1)
    (hsign : ∀ w : ℝ, W ≤ |w| → 0 ≤ σ * stripDensity T w) :
    ∃ M : ℝ, ∀ z : ℂ, |z.im| < c₀ → ‖T z‖ ≤ M := by
  have heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ) := fun a => hevenC a (by simpa using hc₀)
  have hmom := integrable_exp_mul_abs_stripDensity hholo hdec heven hreal hc₀ hax hW hσ hsign
  set M : ℝ := ∫ w : ℝ, Real.exp (2 * π * c₀ * |w|) * |stripDensity T w| with hM
  have hupper : ∀ a y : ℝ, 0 ≤ y → y < c₀ → ‖T ((a : ℂ) + (y : ℂ) * I)‖ ≤ M := by
    intro a y hy0 hy
    refine (norm_strip_line_le hholo hdec heven hy0 hy a).trans ?_
    have hint := integrable_exp_mul_norm_fourier_strip hholo hdec heven hy0 hy
    have hint' : Integrable (fun w : ℝ => Real.exp (-(2 * π * y * w)) *
        ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖) := by
      refine hint.mono' ((by fun_prop : Continuous fun w : ℝ => Real.exp (-(2 * π * y * w))).mul
        (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
          (integrable_strip_real hholo hdec hc₀)).norm).aestronglyMeasurable ?_
      filter_upwards with w
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.exp_le_exp]
      have h1 : -(y * w) ≤ |y * w| := neg_le_abs _
      have h2 : |y * w| = y * |w| := by rw [abs_mul, abs_of_nonneg hy0]
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * π)
      have h4 : -(2 * π * y * w) = 2 * π * -(y * w) := by ring
      have h5 : 2 * π * y * |w| = 2 * π * |y * w| := by rw [h2]; ring
      linarith
    refine integral_mono hint' hmom ?_
    intro w
    show Real.exp (-(2 * π * y * w)) * ‖𝓕 (fun a : ℝ => T (a : ℂ)) w‖ ≤
      Real.exp (2 * π * c₀ * |w|) * |stripDensity T w|
    rw [fourier_eq_stripDensity heven hreal, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Real.exp_le_exp]
    have h1 : -(y * w) ≤ y * |w| := by
      have := neg_le_abs (y * w); rw [abs_mul, abs_of_nonneg hy0] at this; exact this
    have h2 : y * |w| ≤ c₀ * |w| := mul_le_mul_of_nonneg_right hy.le (abs_nonneg w)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0:ℝ) ≤ 2 * π)
    nlinarith [h3]
  refine ⟨M, fun z hz => ?_⟩
  rcases le_total 0 z.im with him | him
  · have hz' : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hz']
    exact hupper z.re z.im him (lt_of_le_of_lt (le_abs_self _) hz)
  · rw [← hevenC z hz]
    have hz' : -z = ((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hz']
    exact hupper (-z.re) (-z.im) (by linarith) (by
      have := neg_abs_le z.im
      have h2 : |z.im| < c₀ := hz
      linarith [abs_lt.mp h2])

/-- **Zeros from unboundedness.**  If an axis-bounded even real source is unbounded on the open
strip, its Fourier transform has real zeros beyond every height. -/
theorem exists_fourier_zero_ge_of_strip_unbounded
    (hholo : ∀ z : ℂ, |z.im| < c₀ → DifferentiableAt ℂ T z)
    (hdec : ∀ β : ℝ, 0 ≤ β → β < c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖T z‖ ≤ C * Real.exp (-|z.re|))
    (hevenC : ∀ z : ℂ, |z.im| < c₀ → T (-z) = T z) (hreal : ∀ a : ℝ, (T (a : ℂ)).im = 0)
    (hc₀ : 0 < c₀) {B₁ : ℝ} (hax : ∀ y : ℝ, 0 ≤ y → y < c₀ → ‖T ((y : ℂ) * I)‖ ≤ B₁)
    (hunb : ∀ M : ℝ, ∃ z : ℂ, |z.im| < c₀ ∧ M < ‖T z‖) (W₀ : ℝ) :
    ∃ w : ℝ, W₀ ≤ w ∧ 𝓕 (fun a : ℝ => T (a : ℂ)) w = 0 := by
  have heven : ∀ a : ℝ, T (-(a : ℂ)) = T (a : ℂ) := fun a => hevenC a (by simpa using hc₀)
  by_contra hno
  push Not at hno
  set W : ℝ := max W₀ 1 with hWdef
  have hW : 0 < W := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hρc := continuous_stripDensity hholo hdec hc₀
  have hρne : ∀ w : ℝ, W ≤ w → stripDensity T w ≠ 0 := by
    intro w hw h0
    apply hno w (le_trans (le_max_left _ _) hw)
    rw [fourier_eq_stripDensity heven hreal, h0, Complex.ofReal_zero]
  set σ : ℝ := if 0 < stripDensity T W then 1 else -1 with hσdef
  have hσ : |σ| = 1 := by rw [hσdef]; split_ifs <;> simp
  have hWval : 0 < σ * stripDensity T W := by
    rw [hσdef]
    split_ifs with h
    · simpa using h
    · have hne := hρne W le_rfl
      have : stripDensity T W < 0 := lt_of_le_of_ne (not_lt.mp h) hne
      linarith
  have hpos : ∀ w : ℝ, W ≤ w → 0 ≤ σ * stripDensity T w := by
    intro w hw
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun v => σ * stripDensity T v) (Set.Icc W w) :=
      (continuous_const.mul hρc).continuousOn
    have hmem : (0 : ℝ) ∈ Set.Icc (σ * stripDensity T w) (σ * stripDensity T W) :=
      ⟨hneg.le, hWval.le⟩
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hw hcont hmem
    have hσ0 : σ ≠ 0 := by intro h; rw [h] at hσ; simp at hσ
    have : stripDensity T c = 0 := by
      have := hc0; simp only at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hσ0
      · exact h
    exact hρne c hc.1 this
  have hsign : ∀ w : ℝ, W ≤ |w| → 0 ≤ σ * stripDensity T w := by
    intro w hw
    rcases le_total 0 w with h | h
    · rw [abs_of_nonneg h] at hw; exact hpos w hw
    · rw [abs_of_nonpos h] at hw
      rw [← stripDensity_neg heven w]
      exact hpos (-w) hw
  obtain ⟨M, hM⟩ := strip_bounded_of_stripDensity_tail_sign hholo hdec hevenC hreal hc₀ hax hW hσ hsign
  obtain ⟨z, hz, hzM⟩ := hunb M
  exact absurd (hM z hz) (not_le.mpr hzM)

end StripHardy

end

end RHTower
