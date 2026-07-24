import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Discrete Abel summation on `Icc 1 N`

`∑_{m=1}^N F(m)·g(m)
   = ∑_{m=1}^N (∑_{k=1}^m F(k))·(g(m) − g(m+1)) + (∑_{k=1}^N F(k))·g(N+1)`.

Summation by parts against the forward difference of `g`, with the
boundary term at `N + 1`; the partial sums of `F` absorb the weight.
-/

namespace HTGeometry

/-- **Discrete Abel summation**: weights trade for partial sums against
the forward difference, plus the boundary term at `N + 1`. -/
theorem sum_mul_eq_partial_mul_diff (F g : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, F m * g m
      = (∑ m ∈ Finset.Icc 1 N,
          (∑ k ∈ Finset.Icc 1 m, F k) * (g m - g (m + 1)))
        + (∑ k ∈ Finset.Icc 1 N, F k) * g (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)
        (fun m => F m * g m), ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)
        (fun m => (∑ k ∈ Finset.Icc 1 m, F k) * (g m - g (m + 1))),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) F]
    ring

end HTGeometry
