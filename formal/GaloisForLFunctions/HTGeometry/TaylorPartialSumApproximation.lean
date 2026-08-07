import Mathlib

/-!
# Polynomial approximation by Taylor partial sums

A function holomorphic on a closed disc is approximated uniformly on any strictly smaller disc by
the partial sums of its Cauchy power series, and those partial sums are polynomials.  This is the
approximation step of the Mittag-Leffler construction: the principal part attached to a pole `a` is
holomorphic on the disc of radius `‖a‖`, so a partial sum of its expansion at the origin
approximates it to within any prescribed tolerance on the disc of radius `‖a‖/2`, and subtracting
that polynomial makes the series of principal parts converge.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

/-- **Uniform polynomial approximation on a smaller disc.**  A function holomorphic on the closed
disc of radius `R` is within `ε` of one of the partial sums of its Cauchy power series, uniformly on
the open disc of radius `r < R`. -/
theorem exists_partialSum_approx {f : ℂ → ℂ} {R : NNReal} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) (R : ℝ)))
    {r : NNReal} (hr : r < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ ball (0 : ℂ) (r : ℝ),
      ‖f z - (cauchyPowerSeries f 0 (R : ℝ)).partialSum n z‖ < ε := by
  have hball := hf.hasFPowerSeriesOnBall hR
  have hrR : ((r : ENNReal)) < ((R : ENNReal)) := by exact_mod_cast hr
  have htu := hball.tendstoUniformlyOn hrR
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp htu ε hε)
  refine ⟨n, fun z hz => ?_⟩
  have h := hn n le_rfl z hz
  rw [dist_eq_norm] at h
  simpa using h

/-- The Cauchy partial sums are polynomial functions: each is a finite sum of monomials. -/
theorem partialSum_eq_sum {f : ℂ → ℂ} {R : ℝ} (n : ℕ) (z : ℂ) :
    (cauchyPowerSeries f 0 R).partialSum n z
      = ∑ i ∈ Finset.range n, (cauchyPowerSeries f 0 R i) fun _ => z := rfl

end GaloisForLFunctions.HTGeometry
