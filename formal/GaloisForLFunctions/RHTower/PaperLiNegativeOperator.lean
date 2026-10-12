import GaloisForLFunctions.RHTower.PaperLiNegativeProfile
import GaloisForLFunctions.HTGeometry.PaperDiagonalCluster

/-! # The full negative Li history in the compact quotient

The proven paper ideal weight is applied to a bounded operator built from every
actual negative Li magnitude. Compact corrections may mix all coefficient indices.
-/

namespace RHTower
noncomputable section
open Classical Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

abbrev PaperLiHistory := lp (fun _ : ℕ => ℂ) 2

def paperLiNegativeOperator (b : PaperLiBudget) : PaperLiHistory →L[ℂ] PaperLiHistory :=
  lpDiagonalCLM (fun n => (paperLiNegativeWeight b n : ℂ)) zero_le_one
    (paperLiNegativeWeight_norm_le b)

@[simp] theorem paperLiNegativeOperator_apply (b : PaperLiBudget) (x : PaperLiHistory) (n : ℕ) :
    paperLiNegativeOperator b x n = (paperLiNegativeWeight b n : ℂ) * x n := rfl

theorem paperLiNegativeOperator_norm_le (b : PaperLiBudget) : ‖paperLiNegativeOperator b‖ ≤ 1 :=
  norm_lpDiagonalCLM_le _ _ _

theorem paperLiNegativeOperator_of_RH (h : RiemannHypothesis) (b : PaperLiBudget) :
    paperLiNegativeOperator b = 0 := by
  ext x n
  simp [paperLiNegativeWeight_of_RH h]

theorem paperLiNegativeOperator_compactIdealDistance (b : PaperLiBudget) :
    compactIdealDistance (paperLiNegativeOperator b) = if RiemannHypothesis then 0 else 1 := by
  classical
  by_cases h : RiemannHypothesis
  · rw [paperLiNegativeOperator_of_RH h, compactIdealDistance_zero, if_pos h]
  · rw [if_neg h]
    apply le_antisymm
    · have he := compactIdealDistance_le (paperLiNegativeOperator b) 0 isCompactOperator_zero
      simp only [sub_zero] at he
      exact he.trans (paperLiNegativeOperator_norm_le b)
    · obtain ⟨j, hj, hw⟩ := paperLiNegativeWeight_escape h b
      simpa only [norm_one, paperLiNegativeOperator] using
        paperDiagonalCluster_le_compactIdealDistance
          (fun n => (paperLiNegativeWeight b n : ℂ)) zero_le_one
          (paperLiNegativeWeight_norm_le b) j hj hw

theorem paperLiNegativeOperator_norm (b : PaperLiBudget) :
    ‖paperLiNegativeOperator b‖ = if RiemannHypothesis then 0 else 1 := by
  classical
  by_cases h : RiemannHypothesis
  · rw [paperLiNegativeOperator_of_RH h, norm_zero, if_pos h]
  · rw [if_neg h]
    apply le_antisymm (paperLiNegativeOperator_norm_le b)
    have he := compactIdealDistance_le (paperLiNegativeOperator b) 0 isCompactOperator_zero
    simpa only [sub_zero, paperLiNegativeOperator_compactIdealDistance, if_neg h] using he

theorem paperLiNegativeOperator_compact_iff (b : PaperLiBudget) :
    IsCompactOperator (paperLiNegativeOperator b) ↔ RiemannHypothesis := by
  constructor
  · intro hc
    by_contra h
    have he := compactIdealDistance_eq_zero_of_isCompactOperator (paperLiNegativeOperator b) hc
    rw [paperLiNegativeOperator_compactIdealDistance, if_neg h] at he
    exact one_ne_zero he
  · intro h
    rw [paperLiNegativeOperator_of_RH h]
    exact isCompactOperator_zero

theorem paperLiNegativeOperator_compact_gap (b : PaperLiBudget)
    (K : compactOperatorStarAlgebra PaperLiHistory) :
    (if RiemannHypothesis then 0 else 1) ≤ ‖paperLiNegativeOperator b - K.1‖ := by
  classical
  rw [← paperLiNegativeOperator_compactIdealDistance]
  exact compactIdealDistance_le _ _ K.2

theorem paperLiNegativeOperator_traceCost (b : PaperLiBudget) :
    compactOperatorTraceCost PaperLiHistory (paperLiNegativeOperator b) =
      if RiemannHypothesis then 0 else ∞ := by
  classical
  rw [compactOperatorTraceCost_eq, paperLiNegativeOperator_compact_iff]

theorem paperLiNegativeOperator_traceCost_add_compact (b : PaperLiBudget)
    (K : compactOperatorStarAlgebra PaperLiHistory) :
    compactOperatorTraceCost PaperLiHistory (paperLiNegativeOperator b + K.1) =
      if RiemannHypothesis then 0 else ∞ := by
  classical
  rw [compactOperatorTraceCost_add_compact, paperLiNegativeOperator_traceCost]

theorem paperLiNegativeOperator_distance_add_compact (b : PaperLiBudget)
    (K : compactOperatorStarAlgebra PaperLiHistory) :
    compactIdealDistance (paperLiNegativeOperator b + K.1) =
      if RiemannHypothesis then 0 else 1 := by
  classical
  rw [paperCompactIdealDistance_add_compact, paperLiNegativeOperator_compactIdealDistance]

end
end RHTower
