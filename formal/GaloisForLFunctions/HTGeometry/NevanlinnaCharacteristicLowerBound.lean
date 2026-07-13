import Mathlib

/-!
# Jensen's inequality for the Nevanlinna characteristic

For a function `f` analytic on a closed disk of radius `r` with `f 0 ≠ 0`, the value `log‖f 0‖`
at the centre is bounded above by the Nevanlinna proximity function `m(r, f) = proximity f ⊤ r`
and hence, for `r ≥ 1`, by the characteristic function `T(r, f) = characteristic f ⊤ r`:

`log‖f 0‖ ≤ m(r, f) ≤ T(r, f)`.

This is the value-distribution form of the sub-mean-value property of `log‖f‖`: the geometric
complexity of `f` on the circle dominates its value at the origin.  The proof combines the
inequality form of Jensen's formula (`AnalyticOnNhd.circleAverage_log_norm`, whose divisor term is
non-negative since an analytic function has non-negative divisor) with `log ≤ log⁺` and the
non-negativity of the logarithmic counting function.
-/

open MeasureTheory Real Complex Metric
open scoped Real

namespace GaloisForLFunctions.Nevanlinna

/-- **Sub-mean-value inequality at radius `r`.**  For `f` analytic on the closed disk of radius
`r > 0` with `f 0 ≠ 0`, `log‖f 0‖` is at most the circle average of `log‖f‖`. -/
theorem log_norm_center_le_circleAverage_log_norm_pos
    (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hf0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ circleAverage (fun z => Real.log ‖f z‖) 0 r := by
  have hrabs : |r| = r := abs_of_pos hr
  have hf' : AnalyticOnNhd ℂ f (closedBall 0 |r|) := by rwa [hrabs]
  have hkey := hf'.circleAverage_log_norm hr.ne' (by simpa using hf0)
  rw [hkey]
  have hdivpos := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf'
  have hsum_nonneg : (0 : ℝ) ≤
      ∑ᶠ u, ((MeromorphicOn.divisor f (closedBall (0:ℂ) |r|)) u : ℝ)
        * Real.log (r * ‖(0:ℂ) - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |r|
    · have hdiv : (0:ℤ) ≤ (MeromorphicOn.divisor f (closedBall (0:ℂ) |r|)) u := hdivpos u
      have hlog : 0 ≤ Real.log (r * ‖(0:ℂ) - u‖⁻¹) := by
        rw [zero_sub, norm_neg]
        rcases eq_or_ne (‖u‖) 0 with h0 | h0
        · simp [h0]
        · apply Real.log_nonneg
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          have hle : ‖u‖ ≤ r := by
            have := mem_closedBall_zero_iff.mp hu; rwa [hrabs] at this
          simpa using hle
      exact mul_nonneg (by exact_mod_cast hdiv) hlog
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]; simp
  linarith

/-- **Jensen's inequality for the proximity function.**  For `f` analytic on the closed disk of
radius `r > 0` with `f 0 ≠ 0`, `log‖f 0‖ ≤ m(r, f)`. -/
theorem log_norm_center_le_proximity
    (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hf0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ ValueDistribution.proximity f ⊤ r := by
  have hrabs : |r| = r := abs_of_pos hr
  have hmero : MeromorphicOn f (sphere 0 |r|) := by
    intro x hx
    rw [hrabs] at hx
    exact hf.meromorphicOn x (sphere_subset_closedBall hx)
  rw [ValueDistribution.proximity_top]
  refine le_trans (log_norm_center_le_circleAverage_log_norm_pos f hr hf hf0) ?_
  apply circleAverage_mono hmero.circleIntegrable_log_norm hmero.circleIntegrable_posLog_norm
  intro x _
  exact le_max_right 0 (Real.log ‖f x‖)

/-- **Jensen's inequality for the Nevanlinna characteristic.**  For `f` analytic on the closed
disk of radius `r ≥ 1` with `f 0 ≠ 0`, `log‖f 0‖ ≤ T(r, f)`. -/
theorem log_norm_center_le_characteristic
    (f : ℂ → ℂ) {r : ℝ} (hr : 1 ≤ r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hf0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ ValueDistribution.characteristic f ⊤ r := by
  refine le_trans (log_norm_center_le_proximity f (by linarith) hf hf0) ?_
  have hlc : (0:ℝ) ≤ ValueDistribution.logCounting f ⊤ r := ValueDistribution.logCounting_nonneg hr
  rw [ValueDistribution.characteristic, Pi.add_apply]
  linarith

/-- **The value at the centre is dominated by the characteristic.**  For `f` analytic on the
closed disk of radius `r ≥ 1` with `f 0 ≠ 0`, `log⁺‖f 0‖ ≤ T(r, f)`.  This is the standard
first-main-theorem corollary bounding the centre value by the Nevanlinna height. -/
theorem posLog_norm_center_le_characteristic
    (f : ℂ → ℂ) {r : ℝ} (hr : 1 ≤ r) (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) (hf0 : f 0 ≠ 0) :
    Real.log⁺ ‖f 0‖ ≤ ValueDistribution.characteristic f ⊤ r :=
  max_le (log_norm_center_le_characteristic f hr hf hf0)
    (ValueDistribution.characteristic_nonneg hr)

end GaloisForLFunctions.Nevanlinna
