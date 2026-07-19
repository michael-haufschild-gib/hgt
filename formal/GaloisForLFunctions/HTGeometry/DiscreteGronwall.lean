import GaloisForLFunctions.HTGeometry.ChainObstruction

/-!
# Discrete Gronwall

The Duhamel identity expresses `Qₙ(w)` in terms of sums over `j ≤ n` — the *same* index as the left
side, not a fixed cut-off.  Coarsening those inner sums to a common `N` (as
`norm_monicOrthoC_duhamel_le_of_le` does) turns the recursion into a single absorption and loses the
index structure; keeping it gives a Gronwall recursion whose solution grows like `exp` of the
displacement rather than blowing up at a finite radius.

This module provides the recursion's solution.
-/

open scoped BigOperators

namespace HTGeometry

/-- The telescoping identity behind the discrete Gronwall bound. -/
theorem prod_one_add_eq_one_add_sum (b : ℕ → ℝ) (N : ℕ) :
    ∏ n ∈ Finset.range N, (1 + b n)
      = 1 + ∑ n ∈ Finset.range N, b n * ∏ k ∈ Finset.range n, (1 + b k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      ring

/-- **Discrete Gronwall.**  A recursion `A N ≤ c + ∑_{n<N} bₙ Aₙ` with nonnegative data is solved by
the product `c ∏_{n<N} (1 + bₙ)`. -/
theorem discrete_gronwall {A b : ℕ → ℝ} {c : ℝ} (hb : ∀ n, 0 ≤ b n)
    (hrec : ∀ N, A N ≤ c + ∑ n ∈ Finset.range N, b n * A n) (N : ℕ) :
    A N ≤ c * ∏ n ∈ Finset.range N, (1 + b n) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      refine le_trans (hrec N) ?_
      have hstep : ∑ n ∈ Finset.range N, b n * A n
          ≤ ∑ n ∈ Finset.range N, b n * (c * ∏ k ∈ Finset.range n, (1 + b k)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact mul_le_mul_of_nonneg_left (ih n (Finset.mem_range.mp hn)) (hb n)
      have h2 : c + ∑ n ∈ Finset.range N, b n * A n
          ≤ c + ∑ n ∈ Finset.range N, b n * (c * ∏ k ∈ Finset.range n, (1 + b k)) := by
        linarith [hstep]
      refine le_trans h2 (le_of_eq ?_)
      rw [prod_one_add_eq_one_add_sum, mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      ring

end HTGeometry
