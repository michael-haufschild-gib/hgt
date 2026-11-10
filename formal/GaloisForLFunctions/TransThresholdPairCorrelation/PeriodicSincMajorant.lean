import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# A periodic majorant for the squared sinc function

The four-mode polynomial majorizes `sinc²` after any dilation by `b ≥ 1`,
with cost `b²`. Its constant coefficient is `3273/4096`; the unused mean
can be added as a nonnegative Fejér kernel when constructing pair densities.

The proof integrates three nonnegative derivatives to obtain the Cusa–Huygens
bound, then uses a factored polynomial upper bound for the square root.
-/

open Real Set

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem nonneg_of_deriv_nonneg_on {f g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc 0 a)) (hd : ∀ x ∈ Ioo 0 a, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Ioo 0 a, 0 ≤ g x) (h0 : f 0 = 0) : 0 ≤ f a := by
  have hm : MonotoneOn f (Icc 0 a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a) (f' := g) hf ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hg x hx
  simpa only [h0] using hm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha

private theorem cusa_huygens {x : ℝ} (hx : 0 ≤ x) (hπ : x ≤ π) :
    3 * sin x ≤ x * (2 + cos x) := by
  have hfirst (a : ℝ) (ha : 0 ≤ a) (haπ : a ≤ π) : 0 ≤ sin a - a * cos a := by
    apply nonneg_of_deriv_nonneg_on ha (by fun_prop)
      (g := fun t => t * sin t)
    · intro t ht
      convert! (hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t)) using 1
      simp [id_eq]
    · intro t ht
      exact mul_nonneg ht.1.le (sin_nonneg_of_mem_Icc ⟨ht.1.le, ht.2.le.trans haπ⟩)
    · simp
  have hsecond (a : ℝ) (ha : 0 ≤ a) (haπ : a ≤ π) :
      0 ≤ 2 - 2 * cos a - a * sin a := by
    apply nonneg_of_deriv_nonneg_on ha (by fun_prop)
      (g := fun t => sin t - t * cos t)
    · intro t ht
      convert! ((hasDerivAt_const t 2).sub ((hasDerivAt_cos t).const_mul 2)).sub
        ((hasDerivAt_id t).mul (hasDerivAt_sin t)) using 1
      simp [id_eq]
      ring
    · intro t ht
      exact hfirst t ht.1.le (ht.2.le.trans haπ)
    · simp
  have hthird : 0 ≤ x * (2 + cos x) - 3 * sin x := by
    apply nonneg_of_deriv_nonneg_on hx (by fun_prop)
      (g := fun t => 2 - 2 * cos t - t * sin t)
    · intro t ht
      convert! ((hasDerivAt_id t).mul ((hasDerivAt_const t 2).add (hasDerivAt_cos t))).sub
        ((hasDerivAt_sin t).const_mul 3) using 1
      simp [id_eq]
      ring
    · intro t ht
      exact hsecond t ht.1.le (ht.2.le.trans hπ)
    · simp
  linarith

/-- A polynomial majorant of the square root on the unit interval. -/
private theorem sqrt_cos_majorant {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c ≤ 1 - (1-c^2)/2 - (1-c^2)^2/8 - (1-c^2)^3/16 - 5*(1-c^2)^4/128 := by
  have h : 0 ≤ (1-c)^5 * (5*c^3+25*c^2+47*c+35) / 128 := by positivity
  have he : (1-c)^5 * (5*c^3+25*c^2+47*c+35) / 128 =
      1 - (1-c^2)/2 - (1-c^2)^2/8 - (1-c^2)^3/16 - 5*(1-c^2)^4/128 - c := by ring
  linarith [he]

/-- A four-mode periodic upper envelope of the squared sinc function. -/
def periodicSincMajorant (x : ℝ) : ℝ :=
  1 - sin x ^ 2 / 3 - sin x ^ 4 / 18 - sin x ^ 6 / 36 - 5 * sin x ^ 8 / 288

theorem cos_envelope_le_majorant (x : ℝ) :
    (2 + |cos x|) ^ 2 / 9 ≤ periodicSincMajorant x := by
  have h := sqrt_cos_majorant (abs_nonneg (cos x)) (abs_cos_le_one x)
  rw [sq_abs] at h
  have hc : cos x ^ 2 = 1 - sin x ^ 2 := by nlinarith only [sin_sq_add_cos_sq x]
  rw [hc] at h
  have he : periodicSincMajorant x - (2 + |cos x|) ^ 2 / 9 =
      4 / 9 * (1 - sin x ^ 2 / 2 - sin x ^ 4 / 8 - sin x ^ 6 / 16 -
        5 * sin x ^ 8 / 128 - |cos x|) := by
    unfold periodicSincMajorant
    nlinarith only [sq_abs (cos x), sin_sq_add_cos_sq x]
  have he' : 1 - (1 - (1 - sin x ^ 2)) / 2 - (1 - (1 - sin x ^ 2)) ^ 2 / 8 -
      (1 - (1 - sin x ^ 2)) ^ 3 / 16 - 5 * (1 - (1 - sin x ^ 2)) ^ 4 / 128 =
      1 - sin x ^ 2 / 2 - sin x ^ 4 / 8 - sin x ^ 6 / 16 - 5 * sin x ^ 8 / 128 := by ring
  rw [he'] at h
  linarith

theorem sinc_sq_le_scaled_cos_envelope {b : ℝ} (hb : 1 ≤ b) (x : ℝ) :
    sinc x ^ 2 ≤ b ^ 2 * ((2 + |cos (b * x)|) ^ 2 / 9) := by
  wlog hx : 0 ≤ x generalizing x
  · simpa only [sinc_neg, mul_neg, cos_neg] using this (-x) (by linarith)
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp only [sinc_zero, mul_zero, cos_zero, abs_one]
    nlinarith only [hb, sq_nonneg (b-1)]
  have hxne : x ≠ 0 := ne_of_gt hxpos
  rw [sinc_of_ne_zero hxne]
  -- Clear the square denominator before splitting into the central interval and its complement.
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
  have hc : 0 ≤ 2 + |cos (b*x)| := by positivity
  have hb0 : 0 < b := by linarith
  by_cases hsmall : b*x ≤ π/2
  · have hxb : x ≤ b*x := by nlinarith only [hb, hx]
    have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos] : -(π/2) ≤ x)
      hsmall hxb
    have hcu := cusa_huygens (mul_nonneg hb0.le hx) (by linarith [pi_pos] : b*x ≤ π)
    have hbound : 3 * sin x ≤ b*x*(2+|cos (b*x)|) := by
      have habs := le_abs_self (cos (b*x))
      nlinarith only [hsin, hcu, mul_nonneg (mul_nonneg hb0.le hx) (sub_nonneg.mpr habs)]
    have hsin0 : 0 ≤ sin x := sin_nonneg_of_mem_Icc ⟨hx, by linarith [pi_pos]⟩
    have hsquare := mul_self_le_mul_self (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hsin0) hbound
    nlinarith only [hsquare]
  · have hfar : 3 ≤ 2*b*x := by linarith [pi_gt_three]
    have hs := (sq_le_one_iff_abs_le_one (sin x)).mpr (abs_sin_le_one x)
    have hsquare := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3) hfar
    have hcos : 4 ≤ (2+|cos (b*x)|)^2 := by nlinarith only [abs_nonneg (cos (b*x))]
    have hm := mul_le_mul_of_nonneg_right hcos (mul_nonneg (sq_nonneg b) (sq_nonneg x))
    nlinarith only [hs, hsquare, hm]

/-- A periodic polynomial with four nonconstant Fourier modes bounds every dilated sinc square. -/
theorem sinc_sq_le_scaled_periodicMajorant {b : ℝ} (hb : 1 ≤ b) (x : ℝ) :
    sinc x ^ 2 ≤ b ^ 2 * periodicSincMajorant (b*x) :=
  (sinc_sq_le_scaled_cos_envelope hb x).trans
    (mul_le_mul_of_nonneg_left (cos_envelope_le_majorant (b*x)) (sq_nonneg b))

/-- Exact Fourier coefficients of the periodic upper envelope. -/
theorem periodicSincMajorant_fourier (x : ℝ) :
    periodicSincMajorant x = 3273/4096 + 991/4608*cos (2*x) - 49/3072*cos (4*x) +
      1/512*cos (6*x) - 5/36864*cos (8*x) := by
  have h2 : cos (2*x) = 1 - 2*sin x^2 := by
    rw [cos_two_mul]
    nlinarith only [sin_sq_add_cos_sq x]
  have h4 : cos (4*x) = 2*cos (2*x)^2-1 := by
    rw [show 4*x = 2*(2*x) by ring, cos_two_mul]
  have h6 : cos (6*x) = 4*cos (2*x)^3-3*cos (2*x) := by
    rw [show 6*x = 3*(2*x) by ring, cos_three_mul]
  have h8 : cos (8*x) = 2*cos (4*x)^2-1 := by
    rw [show 8*x = 2*(4*x) by ring, cos_two_mul]
  rw [h8, h6, h4, h2]
  unfold periodicSincMajorant
  ring


end GaloisForLFunctions.TransThresholdPairCorrelation
