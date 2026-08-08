import Mathlib

/-!
# Cauchy–Schwarz for real integrals, and its weighted form

mathlib carries Hölder's inequality only for `ℝ≥0∞`- and `ℝ≥0`-valued functions
(`ENNReal.lintegral_mul_le_Lp_mul_Lq`), so the plain real statement

`(∫ f g)² ≤ (∫ f²)(∫ g²)`

is not available outside the `Lp` inner-product API.  It needs none of that machinery: the
quadratic `t ↦ ∫ (f + t g)²` is nonnegative, and a nonnegative real quadratic has nonpositive
discriminant.

The weighted form `(∫ w g)² ≤ (∫ w)(∫ w g²)` follows by splitting `w = √w · √w`, and is the
pointwise ingredient of Young's inequality for `L²` convolution.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **A nonnegative quadratic has nonpositive discriminant.** -/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * B * t + C * t ^ 2) : B ^ 2 ≤ A * C := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have hB : B = 0 := by
      by_contra hB
      have ht := h (-(A + 1) / (2 * B))
      rw [← hC0] at ht
      have hcalc : A + 2 * B * (-(A + 1) / (2 * B)) + 0 * (-(A + 1) / (2 * B)) ^ 2 = -1 := by
        field_simp
        ring
      rw [hcalc] at ht
      linarith
    rw [hB, ← hC0]
    simp
  · have ht := h (-B / C)
    have hcalc : A + 2 * B * (-B / C) + C * (-B / C) ^ 2 = A - B ^ 2 / C := by
      field_simp
      ring
    rw [hcalc] at ht
    have h2 : 0 ≤ (A - B ^ 2 / C) * C := mul_nonneg ht hCpos.le
    have h3 : (A - B ^ 2 / C) * C = A * C - B ^ 2 := by field_simp
    linarith [h3 ▸ h2]

variable {μ : Measure ℝ}

/-- A product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_sq_integrable {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ := by
  refine Integrable.mono' (g := fun x => (f x ^ 2 + g x ^ 2) / 2) ((hf2.add hg2).div_const 2)
    (hfm.mul hgm) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

/-- **Cauchy–Schwarz for real integrals.** -/
theorem sq_integral_mul_le {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ y, f y * g y ∂μ) ^ 2 ≤ (∫ y, f y ^ 2 ∂μ) * ∫ y, g y ^ 2 ∂μ := by
  have hfg := integrable_mul_of_sq_integrable hfm hgm hf2 hg2
  have hquad : ∀ t : ℝ, 0 ≤ (∫ y, f y ^ 2 ∂μ) + 2 * (∫ y, f y * g y ∂μ) * t
      + (∫ y, g y ^ 2 ∂μ) * t ^ 2 := by
    intro t
    have hsplit : (fun y => (f y + t * g y) ^ 2)
        = fun y => f y ^ 2 + (2 * t) * (f y * g y) + t ^ 2 * g y ^ 2 := by
      funext y; ring
    have hi1 : Integrable (fun y => f y ^ 2 + (2 * t) * (f y * g y)) μ :=
      hf2.add (hfg.const_mul _)
    have hexp : (∫ y, (f y + t * g y) ^ 2 ∂μ)
        = (∫ y, f y ^ 2 ∂μ) + (2 * t) * (∫ y, f y * g y ∂μ) + t ^ 2 * ∫ y, g y ^ 2 ∂μ := by
      rw [hsplit]
      rw [integral_add hi1 (hg2.const_mul _), integral_add hf2 (hfg.const_mul _),
        integral_const_mul, integral_const_mul]
    have hnn : 0 ≤ ∫ y, (f y + t * g y) ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
    rw [hexp] at hnn
    linarith
  exact sq_le_mul_of_quadratic_nonneg (integral_nonneg fun y => sq_nonneg _) hquad

/-- **The weighted form.**  Against a nonnegative weight, the square of the weighted mean is at
most the total mass times the weighted mean of the square. -/
theorem sq_integral_weighted_le {w g : ℝ → ℝ} (hw : ∀ y, 0 ≤ w y)
    (hwm : AEStronglyMeasurable w μ) (hgm : AEStronglyMeasurable g μ)
    (hwi : Integrable w μ) (hwg2 : Integrable (fun y => w y * g y ^ 2) μ) :
    (∫ y, w y * g y ∂μ) ^ 2 ≤ (∫ y, w y ∂μ) * ∫ y, w y * g y ^ 2 ∂μ := by
  set F : ℝ → ℝ := fun y => Real.sqrt (w y) with hF
  set G : ℝ → ℝ := fun y => Real.sqrt (w y) * g y with hG
  have hFm : AEStronglyMeasurable F μ := (Real.continuous_sqrt.comp_aestronglyMeasurable hwm)
  have hGm : AEStronglyMeasurable G μ := hFm.mul hgm
  have hFsq : (fun y => F y ^ 2) = w := by
    funext y; rw [hF]; exact Real.sq_sqrt (hw y)
  have hGsq : (fun y => G y ^ 2) = fun y => w y * g y ^ 2 := by
    funext y
    rw [hG, mul_pow, Real.sq_sqrt (hw y)]
  have hFG : (fun y => F y * G y) = fun y => w y * g y := by
    funext y
    show Real.sqrt (w y) * (Real.sqrt (w y) * g y) = w y * g y
    rw [← mul_assoc, Real.mul_self_sqrt (hw y)]
  have hf2 : Integrable (fun y => F y ^ 2) μ := by rw [hFsq]; exact hwi
  have hg2 : Integrable (fun y => G y ^ 2) μ := by rw [hGsq]; exact hwg2
  have hmain := sq_integral_mul_le (μ := μ) hFm hGm hf2 hg2
  rw [hFG, hFsq, hGsq] at hmain
  exact hmain

end GaloisForLFunctions.HTGeometry
