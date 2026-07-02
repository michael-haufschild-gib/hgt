/-
# General complex-log estimate: `‖log(1+w)‖ ≤ (1−r)⁻¹·‖w‖` for `‖w‖ ≤ r < 1`

Generalizes `Bottcher.norm_clog_one_add_le` (the `r = 1/2` case) to every radius `r < 1`, by
the same mean-value argument on `closedBall 1 r ⊆ slitPlane` where `‖(log)′‖ = ‖z⁻¹‖ ≤ (1−r)⁻¹`.

Needed by the sharp-threshold window pass: on the sharp far field `{‖w‖ > xStar ‖b‖}` the
series ratio is only bounded by `rMax = ‖b‖/(‖b‖ + xStar) < 1`, which exceeds `1/2` near the
threshold `‖b‖ = 2+√2`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex Metric

namespace U0LogBoundGeneral

/-- **General complex-log estimate**: `‖log(1+w)‖ ≤ (1−r)⁻¹·‖w‖` whenever `‖w‖ ≤ r < 1`. -/
theorem norm_clog_one_add_le_of_le {r : ℝ} (hr : r < 1) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖Complex.log (1 + w)‖ ≤ (1 - r)⁻¹ * ‖w‖ := by
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hw
  have hball : ∀ x ∈ closedBall (1 : ℂ) r, x ∈ slitPlane := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_slitPlane_iff]; left
    have heq : (x - 1).re = x.re - 1 := by rw [Complex.sub_re, Complex.one_re]
    have h1 : |x.re - 1| ≤ ‖x - 1‖ := by rw [← heq]; exact abs_re_le_norm _
    have h2 : |x.re - 1| ≤ r := le_trans h1 hx
    rw [abs_le] at h2; linarith [h2.1]
  have hdiff : ∀ x ∈ closedBall (1 : ℂ) r, DifferentiableAt ℂ Complex.log x :=
    fun x hx => (hasDerivAt_log (hball x hx)).differentiableAt
  have hbound : ∀ x ∈ closedBall (1 : ℂ) r, ‖fderiv ℂ Complex.log x‖ ≤ (1 - r)⁻¹ := by
    intro x hx
    rw [(hasDerivAt_log (hball x hx)).hasFDerivAt.fderiv,
        ContinuousLinearMap.norm_toSpanSingleton, norm_inv]
    have hxn : 1 - r ≤ ‖x‖ := by
      rw [mem_closedBall, dist_eq_norm] at hx
      have h := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one, show (1 : ℂ) - x = -(x - 1) by ring, norm_neg] at h
      linarith [h, hx]
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) hxn
  have h1 : (1 : ℂ) ∈ closedBall (1 : ℂ) r := by simp [mem_closedBall, hr0]
  have h1w : (1 + w) ∈ closedBall (1 : ℂ) r := by
    rw [mem_closedBall, dist_eq_norm]; simpa using hw
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall _ _) h1 h1w
  rw [Complex.log_one, sub_zero] at key
  simpa using key

end U0LogBoundGeneral
