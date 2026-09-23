import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms

/-!
# Supercritical sharpness mechanisms for finite Gibbs packets

Finite Gibbs weights admit both paper mechanisms: density selection finds an average-heavy energy
level, while the exact Wightman geometric-mean identity gives a square-root midpoint alternative
between two endpoint probabilities.
-/

open scoped BigOperators

noncomputable section

namespace HTGeometry

/-- Every nonempty finite Gibbs packet has an energy level of probability at least reciprocal
cardinality. -/
theorem exists_inv_card_le_finiteGibbsStateWeight
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) :
    ∃ a : α, 1 / (Fintype.card α : ℝ) ≤ finiteGibbsStateWeight β energy a := by
  rcases GaloisForLFunctions.HTGeometry.finiteFamilySum_empty_or_le_card_mul
      (finiteGibbsStateWeight β energy) with hzero | ⟨a, ha⟩
  · have hcard : 0 < Fintype.card α := Fintype.card_pos
    omega
  · refine ⟨a, ?_⟩
    rw [sum_finiteGibbsStateWeight_eq_one] at ha
    have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hcard]
    simpa [mul_comm] using ha

/-- Wightman midpoint extraction: for every two energy levels, at least one endpoint Gibbs
probability is no larger than their half-density Wightman weight. -/
theorem finiteGibbsStateWeight_le_wightman_or_le_wightman
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (a b : α) :
    finiteGibbsStateWeight β energy a ≤ finiteKMSWightmanWeight β energy a b ∨
      finiteGibbsStateWeight β energy b ≤ finiteKMSWightmanWeight β energy a b := by
  have hweight : 0 < finiteKMSWightmanWeight β energy a b :=
    finiteKMSWightmanWeight_pos β energy a b
  have hproduct :
      finiteGibbsStateWeight β energy a * finiteGibbsStateWeight β energy b ≤
        finiteKMSWightmanWeight β energy a b ^ (2 : ℕ) :=
    (finiteKMSWightmanWeight_sq β energy a b).symm.le
  have h := GaloisForLFunctions.HTGeometry.le_sqrt_or_le_sqrt_of_mul_le
    (sq_nonneg (finiteKMSWightmanWeight β energy a b)) hproduct
  rw [Real.sqrt_sq hweight.le] at h
  exact h

end HTGeometry
