import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailIsolation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute exponential moments justify integrating strip traces term by
term after restriction to their countable support. Exponential tilting
compensates for real spectral shifts without changing the multiplier. -/

open MeasureTheory Complex
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Exponential tilting spends at most `|α|` in the absolute moment parameter. -/
theorem tilted_abs_weight_le (k : ℝ → ℝ) (α s x : ℝ) :
    Real.exp (s * |x|) * |Real.exp (α * x) * k x| ≤
      Real.exp ((s + |α|) * |x|) * |k x| := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  have h := (le_abs_self (α * x)).trans_eq (abs_mul α x)
  nlinarith only [h]

theorem integrable_tilted_abs_moment {k : ℝ → ℝ} (hk : Continuous k)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|) (α s : ℝ) :
    Integrable fun x => Real.exp (s * |x|) * |Real.exp (α * x) * k x| := by
  apply (hm (s + |α|)).mono'
    (show Continuous (fun x => Real.exp (s * |x|) * |Real.exp (α * x) * k x|) by
      fun_prop).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  exact tilted_abs_weight_le k α s x

theorem tilted_abs_moment_le {k : ℝ → ℝ} (hk : Continuous k)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|) (α s : ℝ) :
    (∫ x, Real.exp (s * |x|) * |Real.exp (α * x) * k x|) ≤
      ∫ x, Real.exp ((s + |α|) * |x|) * |k x| :=
  integral_mono (integrable_tilted_abs_moment hk hm α s) (hm _)
    (tilted_abs_weight_le k α s)

/-- Tilting the kernel compensates exactly for a real shift of the spectrum. -/
theorem integral_tilt_cexp_shift (k : ℝ → ℝ) (α : ℝ) (w : ℂ) :
    (∫ x : ℝ, ((Real.exp (α * x) * k x : ℝ) : ℂ) *
      Complex.exp ((w - (α : ℂ)) * x)) =
      ∫ x : ℝ, (k x : ℂ) * Complex.exp (w * x) := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_mul]
  rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem norm_cexp_strip_le {w : ℂ} {D : ℝ} (hw : |w.re| ≤ D) (x : ℝ) :
    ‖Complex.exp (w * x)‖ ≤ Real.exp (D * |x|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (le_abs_self (w.re * x)).trans
    ((abs_mul w.re x).le.trans (mul_le_mul_of_nonneg_right hw (abs_nonneg x)))

/-- Integration of one translated exponential mode multiplies its coefficient
by the kernel's bilateral Laplace transform. -/
theorem integral_kernel_cexp_re {k : ℝ → ℝ} (hk : Continuous k)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|)
    (c w : ℂ) (t : ℝ) :
    (∫ x, k x * (c * Complex.exp (w * (t + x : ℝ))).re) =
      (c * (∫ x : ℝ, (k x : ℂ) * Complex.exp (w * x)) * Complex.exp (w * t)).re := by
  have hki : Integrable fun x : ℝ => (k x : ℂ) * Complex.exp (w * x) := by
    apply (hm |w.re|).mono'
      (show Continuous (fun x : ℝ => (k x : ℂ) * Complex.exp (w * x)) by
        fun_prop).aestronglyMeasurable
    filter_upwards [] with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (norm_cexp_strip_le (w := w) (le_refl |w.re|) x) (abs_nonneg (k x))
  have hi := hki.const_mul (c * Complex.exp (w * t))
  have hp (x : ℝ) : k x * (c * Complex.exp (w * (t + x : ℝ))).re =
      (c * Complex.exp (w * t) * ((k x : ℂ) * Complex.exp (w * x))).re := by
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [show c * Complex.exp (w * t) * ((k x : ℂ) * Complex.exp (w * x)) =
      (k x : ℂ) * (c * (Complex.exp (w * t) * Complex.exp (w * x))) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [hp]
  have hr := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply] at hr
  rw [hr, integral_const_mul]
  congr 1
  ring

/-- Countable absolutely convergent strip traces commute with positive-kernel
integration; domination is uniform in the spectral index. -/
theorem integral_kernel_cexp_tsum_countable {ι : Type*} [Countable ι]
    (c w : ι → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D)
    {k : ℝ → ℝ} (hk : Continuous k)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|) (t : ℝ) :
    (∫ x, k x * (∑' i, (c i * Complex.exp (w i * (t + x : ℝ))).re)) =
      ∑' i, (c i * (∫ x : ℝ, (k x : ℂ) * Complex.exp (w i * x)) *
        Complex.exp (w i * t)).re := by
  let F : ι → ℝ → ℝ := fun i x => k x * (c i * Complex.exp (w i * (t + x : ℝ))).re
  have hbound (i : ι) (x : ℝ) : ‖F i x‖ ≤
      (‖c i‖ * Real.exp (D * |t|)) * (Real.exp (D * |x|) * |k x|) := by
    by_cases hi : c i = 0
    · simp [F, hi]
    have he : ‖Complex.exp (w i * (t + x : ℝ))‖ ≤
        Real.exp (D * |t|) * Real.exp (D * |x|) := by
      apply (norm_cexp_strip_le (w := w i) (hw i hi) (t + x)).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (abs_add_le t x) hD
      nlinarith only [hh]
    calc
      _ ≤ |k x| * ‖c i * Complex.exp (w i * (t + x : ℝ))‖ := by
        simp only [F, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
      _ ≤ |k x| * (‖c i‖ * (Real.exp (D * |t|) * Real.exp (D * |x|))) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left he (norm_nonneg _)) (abs_nonneg _)
      _ = _ := by ring
  have hFi (i : ι) : Integrable (F i) := by
    apply ((hm D).const_mul (‖c i‖ * Real.exp (D * |t|))).mono'
      (show Continuous (F i) by dsimp [F]; fun_prop).aestronglyMeasurable
    exact Filter.Eventually.of_forall (hbound i)
  have hsum : Summable fun i => ∫ x, ‖F i x‖ := by
    apply Summable.of_norm_bounded
      (hc.mul_right (Real.exp (D * |t|) * (∫ x, Real.exp (D * |x|) * |k x|)))
    intro i
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    have hle := integral_mono (hFi i).norm
      ((hm D).const_mul (‖c i‖ * Real.exp (D * |t|))) (hbound i)
    simpa only [integral_const_mul, mul_assoc] using hle
  have ht := (MeasureTheory.integral_tsum_of_summable_integral_norm hFi hsum).symm
  calc
    _ = ∫ x, ∑' i, F i x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (tsum_mul_left (a := k x)).symm
    _ = ∑' i, ∫ x, F i x := ht
    _ = _ := tsum_congr fun i => integral_kernel_cexp_re hk hm (c i) (w i) t

#print axioms integral_kernel_cexp_tsum_countable

/-- Absolute summability restricts an arbitrary spectral index to countable
support before applying integral interchange. -/
theorem integral_kernel_cexp_tsum {ι : Type*}
    (c w : ι → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D)
    {k : ℝ → ℝ} (hk : Continuous k)
    (hm : ∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|) (t : ℝ) :
    (∫ x, k x * (∑' i, (c i * Complex.exp (w i * (t + x : ℝ))).re)) =
      ∑' i, (c i * (∫ x : ℝ, (k x : ℂ) * Complex.exp (w i * x)) *
        Complex.exp (w i * t)).re := by
  let S : Set ι := Function.support c
  have hSc : S.Countable := by
    simpa only [S, Function.support, norm_ne_zero_iff] using hc.countable_support
  letI : Countable S := hSc.to_subtype
  have hrestrict (f : ι → ℝ) (hf : ∀ i, c i = 0 → f i = 0) :
      (∑' i : S, f i) = ∑' i, f i := by
    apply tsum_subtype_eq_of_support_subset
    intro i hi
    change f i ≠ 0 at hi
    change c i ≠ 0
    exact fun hz => hi (hf i hz)
  calc
    _ = ∫ x, k x * (∑' i : S, (c i * Complex.exp (w i * (t + x : ℝ))).re) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      exact (hrestrict _ (fun i hi => by simp only [hi, zero_mul, Complex.zero_re])).symm
    _ = ∑' i : S, (c i * (∫ x : ℝ, (k x : ℂ) * Complex.exp (w i * x)) *
        Complex.exp (w i * t)).re :=
      integral_kernel_cexp_tsum_countable (fun i : S => c i) (fun i : S => w i)
        hD (hc.subtype S) (fun i hi => hw i hi) hk hm t
    _ = _ := hrestrict (fun i => (c i *
      (∫ x : ℝ, (k x : ℂ) * Complex.exp (w i * x)) * Complex.exp (w i * t)).re)
      (fun i hi => by simp only [hi, zero_mul, Complex.zero_re])

#print axioms integral_kernel_cexp_tsum
#print axioms tilted_abs_moment_le
#print axioms integral_tilt_cexp_shift
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
