import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A rectangular weighted Schur bound

Finite row and column tests control square energy on different index spaces.
Extracted from the deletion-primitive proof for reuse by sharp Hardy kernels.
-/

open scoped BigOperators
namespace GaloisForLFunctions

theorem weighted_rectangular_sum_sq_le {α β : Type*}
    (I : Finset α) (J : Finset β) (T : α → β → ℝ)
    (w : α → ℝ) (v b : β → ℝ) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ n, 0 < v n)
    (hT : ∀ k n, 0 ≤ T k n)
    (hrow : ∀ k ∈ I, ∑ n ∈ J, T k n*v n ≤ C*w k)
    (hcol : ∀ n ∈ J, ∑ k ∈ I, T k n*w k ≤ C*v n) :
    (∑ k ∈ I, (∑ n ∈ J, T k n*b n)^2)  ≤  C^2*∑ n ∈ J, b n^2 := by
  have hpoint (k : α) (hk : k∈I) :
      (∑ n ∈ J, T k n*b n)^2  ≤  C*w k*(∑ n ∈ J, T k n*b n^2/v n) := by
    have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul J
      (f := fun n => T k n*v n) (g := fun n => T k n*b n^2/v n)
      (r := fun n => T k n*b n)
      (fun n _ => mul_nonneg (hT k n) (hv n).le)
      (fun n _ => div_nonneg (mul_nonneg (hT k n) (sq_nonneg _)) (hv n).le)
      (fun n _ => by have hn := (hv n).ne'; field_simp; nlinarith)
    exact hc.trans (mul_le_mul_of_nonneg_right (hrow k hk)
      (Finset.sum_nonneg (fun n _ => div_nonneg (mul_nonneg (hT k n) (sq_nonneg _)) (hv n).le)))
  have heq : (∑ k ∈ I, C*w k*(∑ n ∈ J, T k n*b n^2/v n)) =
      ∑ n ∈ J, C*(b n^2/v n)*(∑ k ∈ I, T k n*w k) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc _  ≤  ∑ k ∈ I, C*w k*(∑ n ∈ J, T k n*b n^2/v n) :=
         Finset.sum_le_sum hpoint
       _ = _ := heq
       _  ≤  ∑ n ∈ J, C^2*b n^2 := by
         apply Finset.sum_le_sum
         intro n hn
         have h := mul_le_mul_of_nonneg_left (hcol n hn)
           (mul_nonneg hC (div_nonneg (sq_nonneg (b n)) (hv n).le))
         have hwne := (hv n).ne'
         calc _ ≤ C*(b n^2/v n)*(C*v n) := h
              _ = _ := by field_simp
       _ = _ := by rw [Finset.mul_sum]

end GaloisForLFunctions
