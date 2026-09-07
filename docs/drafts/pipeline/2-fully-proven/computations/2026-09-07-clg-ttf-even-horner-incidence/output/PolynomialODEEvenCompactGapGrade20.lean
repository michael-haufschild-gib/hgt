import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Exact relative-shear substitution at one modular gap degree -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Gap-degree 20 of the full corrected raw determinant, in fixed units. -/
def evenCompactRawGapGrade20 (_u _w : ℝ) : ℝ :=
  (-913113/4503599627370496000000000000000000 : ℝ)

/-- Exact drift-degree 0 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade20Coeff0 (_v : ℝ) : ℝ :=
  (-913113/4503599627370496000000000000000000 : ℝ)

/-- The relative-shear polynomial retains drift grading. -/
def evenCompactRelativeGapGrade20 (_r v : ℝ) : ℝ :=
  evenCompactRelativeGapGrade20Coeff0 v

/-- Exact symbolic relative-shear identity at this entire gap degree. -/
theorem evenCompactRawGapGrade20_relative_eq (u v : ℝ) :
    evenCompactRawGapGrade20 u (u*(1+v/4)) = evenCompactRelativeGapGrade20 (u^2) v := by
  unfold evenCompactRawGapGrade20 evenCompactRelativeGapGrade20 evenCompactRelativeGapGrade20Coeff0
  ring1

end
end HTGeometry
