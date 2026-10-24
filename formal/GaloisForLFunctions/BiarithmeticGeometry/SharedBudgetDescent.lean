import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Shared capacity and descent from singleton windows

Restriction of a nonnegative allocation preserves a shared upper budget. Gluing locally
admissible allocations does not: every local window may have spent the same resource. On `k`
atoms, universal singleton-to-global descent holds exactly when the budget is zero or `k ≤ 1`.
The sharp excess for `k+1` windows is `k` times the shared budget.
-/

noncomputable section

open Finset
open scoped NNReal

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Each singleton window is allowed to spend the same resource. -/
def SingletonPaymentsGlue (k : ℕ) (B : ℝ≥0) : Prop :=
  ∀ f : Fin k → ℝ, (∀ i, 0 ≤ f i ∧ f i ≤ B) → ∑ i, f i ≤ B

/-- Shared-budget local feasibility is a genuine descent law only in the degenerate cases. -/
theorem singletonPaymentsGlue_iff (k : ℕ) (B : ℝ≥0) :
    SingletonPaymentsGlue k B ↔ k ≤ 1 ∨ B = 0 := by
  constructor
  · intro h
    by_cases hB : B = 0
    · exact Or.inr hB
    · left
      have hBpos : (0 : ℝ) < B := by exact_mod_cast (pos_iff_ne_zero.mpr hB)
      have hsum := h (fun _ => (B : ℝ)) (fun _ => ⟨B.property, le_rfl⟩)
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have hk : (k : ℝ) ≤ 1 := by
        by_contra h
        have hproduct := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hBpos
        nlinarith only [hsum, hproduct]
      exact_mod_cast hk
  · rintro (hk | rfl) f hf
    · have hsum : (∑ i, f i) ≤ (k : ℝ) * B := by
        simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
          (sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin k))) => (hf i).2)
      have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast hk
      exact hsum.trans (by simpa using mul_le_mul_of_nonneg_right hk' B.property)
    · have hf0 : ∀ i, f i = 0 := fun i => le_antisymm (hf i).2 (hf i).1
      simp only [hf0, sum_const_zero, NNReal.coe_zero, le_refl]

/-- Reusing one resource on `k+1` windows has exactly `k*B` worst-case excess. -/
theorem sharedBudget_sharp_excess (k : ℕ) (B : ℝ≥0) :
    ∃ f : Fin (k + 1) → ℝ,
      (∀ i, 0 ≤ f i ∧ f i ≤ B) ∧
      (∑ i, f i) - B = (k : ℝ) * B ∧
      ∀ g : Fin (k + 1) → ℝ, (∀ i, 0 ≤ g i ∧ g i ≤ B) →
        (∑ i, g i) - B ≤ (k : ℝ) * B := by
  refine ⟨fun _ => B, fun _ => ⟨B.property, le_rfl⟩, ?_, ?_⟩
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul, add_sub_cancel_right]
  · intro g hg
    have hsum : (∑ i, g i) ≤ ((k : ℝ) + 1) * B := by
      simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one] using
        (sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin (k + 1)))) => (hg i).2)
    linarith only [hsum]

end GaloisForLFunctions.BiarithmeticGeometry
