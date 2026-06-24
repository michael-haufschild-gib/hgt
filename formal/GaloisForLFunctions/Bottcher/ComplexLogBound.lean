/-
# Böttcher tower — complex-log estimate

The complex analog of the real estimate that drove the Green's-function convergence:

  `‖Complex.log (1 + w)‖ ≤ 2‖w‖`   for `‖w‖ ≤ 1/2`.

Proved by the mean-value inequality on `closedBall 1 (1/2)` (a convex set inside the
slit plane), where `‖(log)′‖ = ‖z⁻¹‖ ≤ 2`. This is brick 1 toward the COMPLEX Böttcher
coordinate `φ_c`: its log-series `∑ 2⁻⁽ⁿ⁺¹⁾·log(1 + c/(f_c^[n]z)²)` converges on the
escape set exactly because these terms are summable, the ℂ-analog of `greenApprox`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex Metric

namespace Bottcher

/-- **Complex-log estimate**: `‖log(1+w)‖ ≤ 2‖w‖` for `‖w‖ ≤ 1/2`. -/
theorem norm_clog_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w)‖ ≤ 2 * ‖w‖ := by
  have hball : ∀ x ∈ closedBall (1 : ℂ) (1 / 2), x ∈ slitPlane := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_slitPlane_iff]; left
    have heq : (x - 1).re = x.re - 1 := by rw [Complex.sub_re, Complex.one_re]
    have h1 : |x.re - 1| ≤ ‖x - 1‖ := by rw [← heq]; exact abs_re_le_norm _
    have : |x.re - 1| ≤ 1 / 2 := le_trans h1 hx
    rw [abs_le] at this; linarith [this.1]
  have hdiff : ∀ x ∈ closedBall (1 : ℂ) (1 / 2), DifferentiableAt ℂ Complex.log x :=
    fun x hx => (hasDerivAt_log (hball x hx)).differentiableAt
  have hbound : ∀ x ∈ closedBall (1 : ℂ) (1 / 2), ‖fderiv ℂ Complex.log x‖ ≤ 2 := by
    intro x hx
    rw [(hasDerivAt_log (hball x hx)).hasFDerivAt.fderiv,
        ContinuousLinearMap.norm_toSpanSingleton, norm_inv]
    have hxn : (1 : ℝ) / 2 ≤ ‖x‖ := by
      rw [mem_closedBall, dist_eq_norm] at hx
      have h := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one, show (1 : ℂ) - x = -(x - 1) by ring, norm_neg] at h
      linarith [h, hx]
    rw [← one_div]
    calc 1 / ‖x‖ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hxn
      _ = 2 := by norm_num
  have h1 : (1 : ℂ) ∈ closedBall (1 : ℂ) (1 / 2) := by simp [mem_closedBall]
  have h1w : (1 + w) ∈ closedBall (1 : ℂ) (1 / 2) := by
    rw [mem_closedBall, dist_eq_norm]; simpa using hw
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall _ _) h1 h1w
  rw [Complex.log_one, sub_zero] at key
  simpa using key

end Bottcher
