import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Discrete Abel summation over a commutative ring

The `Icc 1 N` summation by parts in the generality needed for complex-valued arithmetic weights:
`∑_{m=1}^N F(m)·g(m) = ∑_{m=1}^N (∑_{k=1}^m F(k))·(g(m) − g(m+1)) + (∑_{k=1}^N F(k))·g(N+1)`.
-/

namespace HTGeometry

/-- **Discrete Abel summation over a commutative ring.** -/
theorem sum_mul_eq_partial_mul_diff_ring {R : Type*} [CommRing R] (F g : ℕ → R) (N : ℕ) :
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
