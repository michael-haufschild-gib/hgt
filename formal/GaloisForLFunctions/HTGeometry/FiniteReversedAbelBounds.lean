import GaloisForLFunctions.RHTower.Sieve.AbelInequality
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite and reversed Abel bounds

Only partial sums inside the summation horizon are needed in Abel's inequality.
Reflection then controls a decreasing weight against a finite reversed interval.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- Abel's bound needs partial-sum control only through the final index. -/
theorem abs_sum_mul_le_of_finite_partial {g w : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB : ∀ k ≤ n, |∑ j ∈ range k, g j| ≤ B)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : ∀ i, w (i + 1) ≤ w i) :
    |∑ i ∈ range n, w i * g i| ≤ B * w 0 := by
  let g' : ℕ → ℝ := fun j => if j < n then g j else 0
  have hsum (k : ℕ) : (∑ j ∈ range k, g' j) = ∑ j ∈ range (min k n), g j := by
    dsimp only [g']
    rw [← sum_filter]
    congr 1
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
  have hB' : ∀ k, |∑ j ∈ range k, g' j| ≤ B := fun k => by
    rw [hsum]
    exact hB (min k n) (min_le_right _ _)
  have heq : (∑ i ∈ range n, w i * g' i) = ∑ i ∈ range n, w i * g i := by
    refine sum_congr rfl fun i hi => ?_
    dsimp only [g']
    rw [if_pos (mem_range.mp hi)]
  have h := _root_.RHTower.Sieve.abs_sum_mul_le_of_bounded_partial n hB' hw0 hwanti
  rwa [heq] at h

/-- Reversed finite intervals inherit an Abel bound from interval partial sums. -/
theorem abs_sum_reversed_mul_le {g w : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB : ∀ a b : ℕ, a ≤ b → |∑ j ∈ Ico a b, g j| ≤ B)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : ∀ i, w (i + 1) ≤ w i) :
    |∑ i ∈ range n, w i * g (n - 1 - i)| ≤ B * w 0 := by
  apply abs_sum_mul_le_of_finite_partial n _ hw0 hwanti
  intro k hk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk0 : k = 0 := by omega
    simpa only [hk0, range_zero, sum_empty, Ico_self] using hB 0 0 le_rfl
  · rw [← Nat.Ico_zero_eq_range,
      sum_Ico_reflect g 0 (show k ≤ n - 1 + 1 by omega),
      Nat.sub_add_cancel (show 1 ≤ n from hn), Nat.sub_zero]
    exact hB (n - k) n (Nat.sub_le _ _)

end GaloisForLFunctions.HTGeometry

