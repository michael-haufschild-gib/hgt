import GaloisForLFunctions.HTGeometry.TunablePropagate

/-!
# Controlling the accumulated growth

A chain of tunable transfer steps multiplies the kernel bound by `√((1+εₖ)/(1−δₖ))` at each step, so
the bound after `n` steps carries the product `∏ (1 + aₖ)`.  Since `1 + x ≤ exp x`, that product is
at most `exp (∑ aₖ)`, which is bounded uniformly in `n` whenever the parameters are summable.

This is what turns link 132's summability witness into a uniform bound along the chain.
-/

open scoped BigOperators

namespace HTGeometry

/-- **A product of `1 + aₖ` is controlled by the exponential of the sum.** -/
theorem prod_one_add_le_exp_sum (n : ℕ) {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) :
    ∏ k ∈ Finset.range n, (1 + a k) ≤ Real.exp (∑ k ∈ Finset.range n, a k) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun k _ => by linarith [ha k]) fun k _ => ?_
  have h := Real.add_one_le_exp (a k)
  linarith

/-- With summable parameters the bound is uniform in the number of steps. -/
theorem prod_one_add_le_exp_tsum (n : ℕ) {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hsum : Summable a) :
    ∏ k ∈ Finset.range n, (1 + a k) ≤ Real.exp (∑' k, a k) := by
  refine le_trans (prod_one_add_le_exp_sum n ha) ?_
  refine Real.exp_le_exp.mpr ?_
  exact hsum.sum_le_tsum _ fun k _ => ha k

end HTGeometry
