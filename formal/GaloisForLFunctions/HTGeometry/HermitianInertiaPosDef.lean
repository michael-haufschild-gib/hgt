import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Positive definiteness from Hermitian inertia

For a finite complex Hermitian matrix, vanishing negative and null indices is exactly positive
definiteness.  This is the spectral bridge used by rank-one Schur crossing certificates.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite Hermitian matrix is positive definite exactly when both its negative and null
indices vanish. -/
theorem hermPosDef_iff_negIndex_eq_zero_and_nullIndex_eq_zero {H : Matrix n n ℂ}
    (hH : H.IsHermitian) :
    H.PosDef ↔ hermNegIndex H = 0 ∧ hermNullIndex H = 0 := by
  constructor
  · intro hPos
    constructor
    · rw [negIndex_eq_card_neg_eigenvalues hH]
      apply Finset.card_filter_eq_zero_iff.mpr
      intro i _ hi
      exact (not_lt_of_ge (hPos.eigenvalues_pos i).le) hi
    · rw [nullIndex_eq_card_zero_eigenvalues hH]
      apply Finset.card_filter_eq_zero_iff.mpr
      intro i _ hi
      exact (ne_of_gt (hPos.eigenvalues_pos i)) hi
  · rintro ⟨hNeg, hNull⟩
    apply hH.posDef_iff_eigenvalues_pos.mpr
    have hNoNeg : ∀ i, ¬ hH.eigenvalues i < 0 := by
      rw [negIndex_eq_card_neg_eigenvalues hH] at hNeg
      have h := Finset.card_filter_eq_zero_iff.mp hNeg
      intro i hi
      exact h i (Finset.mem_univ i) hi
    have hNoNull : ∀ i, hH.eigenvalues i ≠ 0 := by
      rw [nullIndex_eq_card_zero_eigenvalues hH] at hNull
      have h := Finset.card_filter_eq_zero_iff.mp hNull
      intro i hi
      exact h i (Finset.mem_univ i) hi
    intro i
    exact lt_of_le_of_ne (le_of_not_gt (hNoNeg i)) (Ne.symm (hNoNull i))

end

end GaloisForLFunctions.HTGeometry
