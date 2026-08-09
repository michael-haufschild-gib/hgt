import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Polynomial approximation on a disc

A function holomorphic on a closed disc is the uniform limit, on every strictly smaller disc, of the
partial sums of its Cauchy power series — and those partial sums are polynomials.  So on a disc no
Runge theorem is needed: the power series already supplies polynomial approximation.

This is the base case of polynomial Runge.  What Runge adds is the passage to a compact set that is
not a disc, where the Cauchy kernel has poles that must be pushed out along the complement.

* `HTGeometry.tendstoUniformlyOn_cauchyPartialSum`;
* `HTGeometry.exists_partialSum_approx_on_closedBall`.
-/

open Metric

namespace HTGeometry

/-- **Uniform approximation on a disc by the partial sums of the Cauchy series.** -/
theorem tendstoUniformlyOn_cauchyPartialSum {R : NNReal} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R)) {r : NNReal} (hr : r < R) :
    TendstoUniformlyOn (fun n y => (cauchyPowerSeries f 0 (R : ℝ)).partialSum n y) f
      Filter.atTop (ball (0 : ℂ) (r : ℝ)) := by
  have hball := hf.hasFPowerSeriesOnBall hR
  have hlt : (r : ENNReal) < (R : ENNReal) := by exact_mod_cast hr
  have hunif := hball.tendstoUniformlyOn hlt
  refine hunif.congr_right fun y _ => ?_
  simp

/-- **A polynomial partial sum within any prescribed error on a closed disc.** -/
theorem exists_partialSum_approx_on_closedBall {R : NNReal} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R)) {r : NNReal} (hr : r < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) (r : ℝ),
      ‖f z - (cauchyPowerSeries f 0 (R : ℝ)).partialSum n z‖ < ε := by
  obtain ⟨r', hrr', hr'R⟩ := exists_between hr
  have hunif := tendstoUniformlyOn_cauchyPartialSum hR hf hr'R
  have hmem := hunif ε hε
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hmem
  refine ⟨n, fun z hz => ?_⟩
  have hzball : z ∈ ball (0 : ℂ) (r' : ℝ) := by
    have hzr : ‖z‖ ≤ (r : ℝ) := by simpa using mem_closedBall_zero_iff.1 hz
    have : (r : ℝ) < (r' : ℝ) := by exact_mod_cast hrr'
    rw [mem_ball_zero_iff]
    linarith
  have hval := hn n le_rfl z hzball
  rw [Complex.dist_eq] at hval
  exact hval

end HTGeometry
