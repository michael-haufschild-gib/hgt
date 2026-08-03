import GaloisForLFunctions.HTGeometry.ClockIterateBound

/-!
# The sum of the iterates

The bound carried by the iterates is dominated by a geometric series, so on a rectangle small
compared with the radius of analyticity the series

`u(ξ, η, z) = ∑ₘ W_m(ξ, η, z)`

converges absolutely. This file defines that sum and proves the convergence. The rectangle is
two-sided: only `|ξ|, |η| ≤ T` is asked, so the series converges on a neighbourhood of the origin.

The smallness condition is the one the convergence estimate predicts: with `K = 4 + ‖V‖ρ₀²/4` and a
rectangle of side at most `T`, the series converges as soon as `K T² e² < (ρ₀ - ρ)²`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The solution of the characteristic clock equation, as the sum of the iterates. -/
noncomputable def clockSolution (V : ℂ → ℂ) (ξ η : ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, clockIterate V m ξ η z

/-- **The series of iterates converges absolutely on a small rectangle.** -/
theorem summable_clockIterate {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℂ → ℂ}
    (hVc : ContinuousOn V (imStrip ρ₀)) (hVd : DifferentiableOn ℂ V (imStrip ρ₀))
    (hMv0 : 0 ≤ Mv) (hMv : ∀ z ∈ imStrip ρ₀, ‖V z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / (ρ₀ - ρ) ^ 2 < 1)
    {s t : ℝ} (hsT : |s| ≤ T) (htT : |t| ≤ T)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    Summable fun m : ℕ => clockIterate V m s t z := by
  have hK0 : (0 : ℝ) ≤ 4 + Mv * ρ₀ ^ 2 / 4 := by positivity
  have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
  have hmaj := summable_ovsyannikov_bound (K := 4 + Mv * ρ₀ ^ 2 / 4) (G := ρ₀ - ρ) (T := T)
    hK0 hG hT hsmall
  refine Summable.of_norm_bounded hmaj fun m => ?_
  have hbase := clockIterate_norm_le hρ₀ hVc hVd hMv0 hMv m ρ hρ0 hρ s t z hz
  refine hbase.trans ?_
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  gcongr

end GaloisForLFunctions.HTGeometry
