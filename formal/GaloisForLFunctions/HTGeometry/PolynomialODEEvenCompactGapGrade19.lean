import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Exact relative-shear substitution at one modular gap degree -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Gap-degree 19 of the full corrected raw determinant, in fixed units. -/
def evenCompactRawGapGrade19 (u w : ℝ) : ℝ :=
  (((-620129493/703687441776640000000000000000000000 : ℝ) +
    (-579868821/703687441776640000000000000000000000 : ℝ)*w^(2 : ℕ) : ℝ) +
    ((-1292162211/351843720888320000000000000000000000 : ℝ)*u^(1 : ℕ)*w^(1 : ℕ) +
    (-775199451/703687441776640000000000000000000000 : ℝ)*u^(2 : ℕ) : ℝ) : ℝ)

/-- Exact drift-degree 0 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade19Coeff0 (_v : ℝ) : ℝ :=
  (-620129493/703687441776640000000000000000000000 : ℝ)

/-- Exact drift-degree 1 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade19Coeff1 (v : ℝ) : ℝ :=
  ((-1969696347/351843720888320000000000000000000000 : ℝ) +
    ((-234003879/175921860444160000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (-579868821/11258999068426240000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ)

/-- The relative-shear polynomial retains drift grading. -/
def evenCompactRelativeGapGrade19 (r v : ℝ) : ℝ :=
  (evenCompactRelativeGapGrade19Coeff0 v +
    (r^(1 : ℕ)*evenCompactRelativeGapGrade19Coeff1 v) : ℝ)

/-- Exact symbolic relative-shear identity at this entire gap degree. -/
theorem evenCompactRawGapGrade19_relative_eq (u v : ℝ) :
    evenCompactRawGapGrade19 u (u*(1+v/4)) = evenCompactRelativeGapGrade19 (u^(2 : ℕ)) v := by
  unfold evenCompactRawGapGrade19 evenCompactRelativeGapGrade19 evenCompactRelativeGapGrade19Coeff0 evenCompactRelativeGapGrade19Coeff1
  ring1

end
end HTGeometry
