import GaloisForLFunctions.HTGeometry.PaperRotationClosedAlgebra
import GaloisForLFunctions.HTGeometry.PaperRotationShiftEscape
import GaloisForLFunctions.HTGeometry.CompactCofinalEssentialMargin

/-!
# Faithfulness of the rotation algebra modulo compact operators

Every member of the full norm-closed rotation algebra has essential norm equal to its operator
norm. Return-time conjugations recover the member in norm, whereas compact corrections vanish
strongly along the same shifts. The proven paper ideal trace therefore costs zero exactly at
the zero algebra element, and infinity at every nonzero element.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped ENNReal Classical

/-- Compact conjugates vanish strongly along the same integer returns as the algebra. -/
theorem paperRotation_compact_conjugation_tendsto (t : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (v : PaperRotationHilbert) :
    Tendsto (fun n => paperRotationConjugation (paperRotationReturnTime t n : ℤ) K.1 v)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (paperRotationShift_compact_tendsto K v).comp (paperRotationReturnTime_tendsto t)
  simpa only [Function.comp_def, paperRotationConjugation_apply, paperRotationShift_norm] using
    tendsto_zero_iff_norm_tendsto_zero.mp h

/-- No compact correction can reduce the operator norm of a rotation algebra element. -/
theorem paperRotationAlgebra_norm_le_sub_compact (t : ℝ) (A : paperRotationAlgebra t)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) :
    ‖A.1‖ ≤ ‖A.1 - K.1‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
  intro v hv
  have hA : Tendsto
      (fun n => paperRotationConjugation (paperRotationReturnTime t n : ℤ) A.1 v)
      atTop (𝓝 (A.1 v)) :=
    ((ContinuousLinearMap.apply ℂ PaperRotationHilbert v).continuous.tendsto A.1).comp
      (paperRotationAlgebra_conjugation_tendsto t A)
  have hK := paperRotation_compact_conjugation_tendsto t K v
  have h := (hA.sub hK).norm
  simp only [sub_zero] at h
  apply le_of_tendsto' h
  intro n
  have he : paperRotationConjugation (paperRotationReturnTime t n : ℤ) A.1 v -
      paperRotationConjugation (paperRotationReturnTime t n : ℤ) K.1 v =
      paperRotationConjugation (paperRotationReturnTime t n : ℤ) (A.1 - K.1) v := by
    rw [map_sub, sub_apply]
  rw [he]
  simpa only [hv, mul_one, paperRotationConjugation_norm] using
    (paperRotationConjugation (paperRotationReturnTime t n : ℤ) (A.1 - K.1)).le_opNorm v

/-- The quotient by compact operators preserves the full norm of every algebra element. -/
theorem paperRotationAlgebra_compactIdealDistance (t : ℝ) (A : paperRotationAlgebra t) :
    compactIdealDistance A.1 = ‖A.1‖ := by
  apply le_antisymm
  · simpa using compactIdealDistance_le A.1 0 isCompactOperator_zero
  · exact le_compactIdealDistance A.1 ‖A.1‖ fun K hK =>
      paperRotationAlgebra_norm_le_sub_compact t A ⟨K, hK⟩

/-- The full rotation algebra meets the compact ideal only at zero. -/
theorem paperRotationAlgebra_compact_iff_zero (t : ℝ) (A : paperRotationAlgebra t) :
    IsCompactOperator A.1 ↔ A = 0 := by
  constructor
  · intro h
    have hn := paperRotationAlgebra_norm_le_sub_compact t A ⟨A.1, h⟩
    rw [sub_self, norm_zero] at hn
    apply Subtype.ext
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  · rintro rfl
    exact isCompactOperator_zero

/-- Equality modulo compact operators is literal equality throughout the closed algebra. -/
theorem paperRotationAlgebra_compact_sub_iff_eq (t : ℝ)
    (A B : paperRotationAlgebra t) :
    IsCompactOperator (A.1 - B.1) ↔ A = B := by
  change IsCompactOperator (A - B).1 ↔ _
  rw [paperRotationAlgebra_compact_iff_zero, sub_eq_zero]

/-- The compact quotient preserves distances, not only norms at the origin. -/
theorem paperRotationAlgebra_compactIdealDistance_sub (t : ℝ)
    (A B : paperRotationAlgebra t) :
    compactIdealDistance (A.1 - B.1) = dist A B := by
  simpa [dist_eq_norm] using paperRotationAlgebra_compactIdealDistance t (A - B)

/-- The proven paper ideal trace is faithful on the entire represented rotation algebra. -/
theorem paperRotationAlgebra_traceCost (t : ℝ) (A : paperRotationAlgebra t) :
    compactOperatorTraceCost PaperRotationHilbert A.1 = if A = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperRotationAlgebra_compact_iff_zero]
  split_ifs <;> rfl

/-- Finite paper ideal cost forces the zero algebra element. This weight alone therefore cannot
provide a nonzero finite arithmetic count on the represented rotation algebra. -/
theorem paperRotationAlgebra_traceCost_lt_top_iff (t : ℝ) (A : paperRotationAlgebra t) :
    compactOperatorTraceCost PaperRotationHilbert A.1 < ∞ ↔ A = 0 := by
  rw [compactOperatorTraceCost_lt_top_iff, paperRotationAlgebra_compact_iff_zero]

/-- Arbitrary compact corrections preserve this exact zero-versus-infinite classification. -/
theorem paperRotationAlgebra_traceCost_add_compact (t : ℝ) (A : paperRotationAlgebra t)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) :
    compactOperatorTraceCost PaperRotationHilbert (A.1 + K.1) =
      if A = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperRotationAlgebra_traceCost]

end

end GaloisForLFunctions.HTGeometry
