import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Abs

/-!
# Abel summation, as a finite identity

Summation by parts in the shape the ray calculus keeps needing: the weight moves off the
coefficients and onto their partial sums, leaving one boundary term and the increments of the
weight.

`∑_{n ≤ N} a_n f_n = A_N f_N + ∑_{n < N} A_n (f_n - f_{n+1})`

Every Abel argument in the Möbius calculus — the preimage estimate, the harmonic series, the
Dirichlet series — is this identity followed by a limit.

* `deningerAbelSummation` : **the finite summation-by-parts identity.**
-/

namespace RHTower

noncomputable section

/-- The partial sums of a coefficient sequence. -/
def deningerPartialSum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), a n

@[simp]
theorem deningerPartialSum_zero (a : ℕ → ℝ) : deningerPartialSum a 0 = a 0 := by
  rw [deningerPartialSum]
  simp

/-- **Abel summation.**  The weight moves onto the partial sums, leaving one boundary term and the
increments of the weight. -/
theorem deningerAbelSummation (a f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * f n)
      = deningerPartialSum a N * f N
        + ∑ n ∈ Finset.range N, deningerPartialSum a n * (f n - f (n + 1)) := by
  have hbp := Finset.sum_range_by_parts f a (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hbp
  have hlhs : (∑ n ∈ Finset.range (N + 1), a n * f n)
      = ∑ n ∈ Finset.range (N + 1), f n * a n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hinner : ∀ n ∈ Finset.range N,
      (f (n + 1) - f n) * (∑ k ∈ Finset.range (n + 1), a k)
        = -(deningerPartialSum a n * (f n - f (n + 1))) := by
    intro n _
    rw [deningerPartialSum]
    ring
  rw [hlhs, hbp, Finset.sum_congr rfl hinner, Finset.sum_neg_distrib, deningerPartialSum]
  ring

/-- The boundary term of Abel summation, isolated. -/
theorem deningerAbelSummation_boundary (a f : ℕ → ℝ) (N : ℕ) :
    deningerPartialSum a N * f N
      = (∑ n ∈ Finset.range (N + 1), a n * f n)
        - ∑ n ∈ Finset.range N, deningerPartialSum a n * (f n - f (n + 1)) := by
  rw [deningerAbelSummation a f N]
  ring

end

end RHTower
