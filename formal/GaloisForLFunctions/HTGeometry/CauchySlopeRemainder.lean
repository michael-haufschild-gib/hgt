import GaloisForLFunctions.Bottcher.Montel
import Mathlib.Analysis.Calculus.MeanValue

/-! # Cauchy control of a literal difference-quotient remainder

Two Cauchy derivative estimates and the complex mean-value inequality give
one remainder modulus proportional to the original pointwise majorant.
Applying this to spatial increments preserves a common variation control.
-/

noncomputable section
open Set Metric Complex

namespace GaloisForLFunctions.HTGeometry

theorem norm_cauchySlopeRemainder_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z : ℂ) (B : ℝ) (hB : ∀ w ∈ ball z 1, ‖f w‖ ≤ B)
    {h : ℂ} (hh : h ≠ 0) (hsmall : ‖h‖ < 1/4) :
    ‖h⁻¹ * (f (z+h)-f z) - deriv f z‖ ≤ 8*B*‖h‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z (mem_ball_self one_pos))
  have hd (w : ℂ) (hw : w ∈ ball z (1/2)) : ‖deriv f w‖ ≤ 2*B := by
    simpa only [div_one] using
      Bottcher.norm_deriv_le_of_bounded_on_ball one_pos hf.differentiableOn hB w hw
  have hdd (w : ℂ) (hw : w ∈ ball z (1/4)) : ‖deriv (deriv f) w‖ ≤ 8*B := by
    have hw' : w ∈ ball z ((1/2)/2) := by convert hw using 1; norm_num
    have he := Bottcher.norm_deriv_le_of_bounded_on_ball (by norm_num : (0:ℝ)<1/2)
      hf.deriv.differentiableOn hd w hw'
    convert he using 1; ring
  have hsub : closedBall z ‖h‖ ⊆ ball z (1/4) := by
    intro w hw
    exact (mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hsmall))
  have hz : z ∈ closedBall z ‖h‖ := mem_closedBall_self (norm_nonneg _)
  have hz' : z+h ∈ closedBall z ‖h‖ := by simp only [mem_closedBall, dist_self_add_left, le_refl]
  have hdiff (w : ℂ) (hw : w ∈ closedBall z ‖h‖) :
      ‖deriv f w - deriv f z‖ ≤ 8*B*‖h‖ := by
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u (_ : u ∈ closedBall z ‖h‖) => (hf.deriv u).hasDerivAt.hasDerivWithinAt)
      (fun u hu => hdd u (hsub hu)) (convex_closedBall z ‖h‖) hz hw
    exact he.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using mem_closedBall.mp hw)
      (mul_nonneg (by norm_num) hB0))
  let g : ℂ → ℂ := fun w => f w - (w-z)*deriv f z
  have hg (w : ℂ) : HasDerivAt g (deriv f w - deriv f z) w := by
    simpa only [g, one_mul] using!
      (hf w).hasDerivAt.sub (((hasDerivAt_id w).sub_const z).mul_const (deriv f z))
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w (_ : w ∈ closedBall z ‖h‖) => (hg w).hasDerivWithinAt)
    hdiff (convex_closedBall z ‖h‖) hz hz'
  have he' : ‖f (z+h)-f z-h*deriv f z‖ ≤ (8*B*‖h‖)*‖h‖ := by
    simpa only [g, add_sub_cancel_left, sub_self, zero_mul, sub_zero,
      sub_right_comm, add_sub_cancel_left] using he
  have hid : h⁻¹*(f (z+h)-f z)-deriv f z =
      h⁻¹*(f (z+h)-f z-h*deriv f z) := by
    conv_rhs => rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hh, one_mul]
  rw [hid, norm_mul, norm_inv]
  calc
    _ ≤ ‖h‖⁻¹*((8*B*‖h‖)*‖h‖) := mul_le_mul_of_nonneg_left he' (by positivity)
    _ = 8*B*‖h‖ := by
      rw [mul_comm (8*B*‖h‖) ‖h‖, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh), one_mul]

end GaloisForLFunctions.HTGeometry
