import GaloisForLFunctions.RHTower.PaperDeningerFramedCurvature
import GaloisForLFunctions.HTGeometry.PaperHilbertOffDiagonal

/-! # The full nilpotent completion of normalized framed mate curvature

Every degree and both native matrix channels are retained. Compact corrections
may mix all coordinates. The quotient has exactly the signed limiting classes
of the literal mate profile, even though the operator is square-zero.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry Filter Topology
open scoped ENNReal

def paperDeningerMateDiagonal (s : ℂ) : PaperCornerSource →L[ℂ] PaperCornerSource :=
  paperConvergentDiagonal (fun j => (paperDeningerMateWeight s j : ℂ))
    (paperDeningerMateWeight_complex_tendsto s)

def paperDeningerMateOperator (s : ℂ) : PaperCornerSpace →L[ℂ] PaperCornerSpace :=
  paperHilbertOffDiagonal (paperDeningerMateDiagonal s)

theorem paperDeningerMateOperator_apply (s : ℂ) (x : PaperCornerSpace) (j : ℕ) (b : Fin 2) :
    paperDeningerMateOperator s x (j, b) =
      if b = 0 then (paperDeningerMateWeight s j : ℂ) * x (j, 1) else 0 := by
  simp [paperDeningerMateOperator, paperHilbertOffDiagonal, paperCornerInjection_apply,
    paperDeningerMateDiagonal, paperConvergentDiagonal_apply]

theorem paperDeningerMateOperator_native_entry (s : ℂ) (x : PaperCornerSpace) (j : ℕ) :
    paperDeningerMateOperator s x (j, 0) =
      (paperDeningerNormalizedFrame s j 0 1 : ℂ) * x (j, 1) := by
  simp [paperDeningerMateOperator_apply]

theorem paperDeningerMateOperator_sq (s : ℂ) : paperDeningerMateOperator s ^ 2 = 0 :=
  paperHilbertOffDiagonal_sq _

theorem paperDeningerMateOperator_critical (s : ℂ) (h : s.re = 1 / 2) :
    paperDeningerMateOperator s = 0 := by
  ext x p
  rcases p with ⟨j, b⟩
  simp [paperDeningerMateOperator_apply, paperDeningerMateWeight_critical s h]

theorem paperDeningerMateOperator_norm_le (s : ℂ) : ‖paperDeningerMateOperator s‖ ≤ 1 := by
  rw [paperDeningerMateOperator, paperHilbertOffDiagonal_norm]
  have hb (j : ℕ) : ‖(paperDeningerMateWeight s j : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (abs_paperDeningerMateWeight_lt_one s j).le
  have he : paperDeningerMateDiagonal s =
      GaloisForLFunctions.lpDiagonalCLM (fun j => (paperDeningerMateWeight s j : ℂ)) zero_le_one hb := by
    ext x j
    rfl
  rw [he]
  exact GaloisForLFunctions.norm_lpDiagonalCLM_le _ _ _

theorem paperDeningerMateOperator_compact_iff (s : ℂ) :
    IsCompactOperator (paperDeningerMateOperator s) ↔ s.re = 1 / 2 := by
  rw [paperDeningerMateOperator, paperHilbertOffDiagonal_compact_iff,
    paperDeningerMateDiagonal, paperConvergentDiagonal_compact_iff,
    Complex.ofReal_eq_zero, paperDeningerMateLimit_eq_zero_iff]

theorem paperDeningerMateOperator_compactIdealDistance (s : ℂ) :
    compactIdealDistance (paperDeningerMateOperator s) = if s.re = 1 / 2 then 0 else 1 := by
  rw [paperDeningerMateOperator, paperHilbertOffDiagonal_compactIdealDistance,
    paperDeningerMateDiagonal, paperConvergentDiagonal_compactIdealDistance,
    norm_paperDeningerMateLimit]

theorem paperDeningerMateOperator_norm (s : ℂ) :
    ‖paperDeningerMateOperator s‖ = if s.re = 1 / 2 then 0 else 1 := by
  by_cases h : s.re = 1 / 2
  · simp [paperDeningerMateOperator_critical s h, h]
  · rw [if_neg h]
    apply le_antisymm (paperDeningerMateOperator_norm_le s)
    have he := compactIdealDistance_le (paperDeningerMateOperator s) 0 isCompactOperator_zero
    rwa [paperDeningerMateOperator_compactIdealDistance, if_neg h, sub_zero] at he

/-- Arbitrary compact mixing of all degrees and channels cannot remove the gap. -/
theorem paperDeningerMateOperator_compact_gap (s : ℂ)
    (K : compactOperatorStarAlgebra PaperCornerSpace) :
    (if s.re = 1 / 2 then 0 else 1) ≤ ‖paperDeningerMateOperator s - K.1‖ := by
  rw [← paperDeningerMateOperator_compactIdealDistance]
  exact compactIdealDistance_le _ _ K.2

theorem paperDeningerMateOperator_traceCost (s : ℂ) :
    compactOperatorTraceCost PaperCornerSpace (paperDeningerMateOperator s) =
      if s.re = 1 / 2 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperDeningerMateOperator_compact_iff]

theorem paperDeningerMateOperator_traceCost_add_compact (s : ℂ)
    (K : compactOperatorStarAlgebra PaperCornerSpace) :
    compactOperatorTraceCost PaperCornerSpace (paperDeningerMateOperator s + K.1) =
      if s.re = 1 / 2 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperDeningerMateOperator_traceCost]

/-- The compact quotient retains exactly the three signed limiting characters. -/
theorem paperDeningerMateOperator_compact_sub_iff (s t : ℂ) :
    IsCompactOperator (paperDeningerMateOperator s - paperDeningerMateOperator t) ↔
      paperDeningerMateLimit s = paperDeningerMateLimit t := by
  rw [paperDeningerMateOperator, paperDeningerMateOperator, ← paperHilbertOffDiagonal_sub,
    paperHilbertOffDiagonal_compact_iff, paperDeningerMateDiagonal, paperDeningerMateDiagonal,
    paperConvergentDiagonal_compact_sub_iff, Complex.ofReal_inj]

theorem paperDeningerMateOperator_compactIdealDistance_sub (s t : ℂ) :
    compactIdealDistance (paperDeningerMateOperator s - paperDeningerMateOperator t) =
      |paperDeningerMateLimit s - paperDeningerMateLimit t| := by
  rw [paperDeningerMateOperator, paperDeningerMateOperator, ← paperHilbertOffDiagonal_sub,
    paperHilbertOffDiagonal_compactIdealDistance, paperDeningerMateDiagonal, paperDeningerMateDiagonal,
    paperConvergentDiagonal_compactIdealDistance_sub, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

theorem paperDeningerMateOperator_compact_same_right (s t : ℂ)
    (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    IsCompactOperator (paperDeningerMateOperator s - paperDeningerMateOperator t) := by
  rw [paperDeningerMateOperator_compact_sub_iff]
  simp only [paperDeningerMateLimit, if_neg (ne_of_gt hs), if_neg (ne_of_gt ht),
    if_neg (not_lt_of_ge hs.le), if_neg (not_lt_of_ge ht.le)]

theorem paperDeningerMateOperator_compact_same_left (s t : ℂ)
    (hs : s.re < 1 / 2) (ht : t.re < 1 / 2) :
    IsCompactOperator (paperDeningerMateOperator s - paperDeningerMateOperator t) := by
  rw [paperDeningerMateOperator_compact_sub_iff]
  simp only [paperDeningerMateLimit, if_neg (ne_of_lt hs), if_neg (ne_of_lt ht), if_pos hs, if_pos ht]

theorem paperDeningerMateOperator_opposite_gap (s t : ℂ)
    (hs : s.re < 1 / 2) (ht : 1 / 2 < t.re) :
    compactIdealDistance (paperDeningerMateOperator s - paperDeningerMateOperator t) = 2 := by
  rw [paperDeningerMateOperator_compactIdealDistance_sub]
  simp only [paperDeningerMateLimit, if_neg (ne_of_lt hs), if_neg (ne_of_gt ht),
    if_pos hs, if_neg (not_lt_of_ge ht.le)]
  norm_num

end
end RHTower
