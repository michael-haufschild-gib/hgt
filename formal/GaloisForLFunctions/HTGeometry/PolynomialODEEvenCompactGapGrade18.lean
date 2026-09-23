import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Exact relative-shear substitution at one modular gap degree -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Gap-degree 18 of the full corrected raw determinant, in fixed units. -/
def evenCompactRawGapGrade18 (u w : ℝ) : ℝ :=
  ((((-57754209573/8796093022208000000000000000000000000 : ℝ) +
    (577411635807/8796093022208000000000000000000000000 : ℝ)*w^(2 : ℕ) : ℝ) +
    ((83499748533/17592186044416000000000000000000000000 : ℝ)*w^(4 : ℕ) +
    (-283407993513/4398046511104000000000000000000000000 : ℝ)*u^(1 : ℕ)*w^(1 : ℕ) : ℝ) : ℝ) +
    (((-117531128997/4398046511104000000000000000000000000 : ℝ)*u^(1 : ℕ)*w^(3 : ℕ) +
    (176687542017/8796093022208000000000000000000000000 : ℝ)*u^(2 : ℕ) : ℝ) +
    ((-22254531057/1099511627776000000000000000000000000 : ℝ)*u^(2 : ℕ)*w^(2 : ℕ) +
    ((-49925249991/2199023255552000000000000000000000000 : ℝ)*u^(3 : ℕ)*w^(1 : ℕ) +
    (-174157177861/52776558133248000000000000000000000000 : ℝ)*u^(4 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- Exact drift-degree 0 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade18Coeff0 (_v : ℝ) : ℝ :=
  (-57754209573/8796093022208000000000000000000000000 : ℝ)

/-- Exact drift-degree 1 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade18Coeff1 (v : ℝ) : ℝ :=
  ((93641595399/4398046511104000000000000000000000000 : ℝ) +
    ((147001821147/8796093022208000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (577411635807/140737488355328000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ)

/-- Exact drift-degree 2 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade18Coeff2 (v : ℝ) : ℝ :=
  (((-1800227485373/26388279066624000000000000000000000000 : ℝ) +
    (-34186274181/1099511627776000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((-632723776839/140737488355328000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    ((-2126961279/17592186044416000000000000000000000000 : ℝ)*v^(3 : ℕ) +
    (83499748533/4503599627370496000000000000000000000000 : ℝ)*v^(4 : ℕ) : ℝ) : ℝ) : ℝ)

/-- The relative-shear polynomial retains drift grading. -/
def evenCompactRelativeGapGrade18 (r v : ℝ) : ℝ :=
  (evenCompactRelativeGapGrade18Coeff0 v +
    ((r^(1 : ℕ)*evenCompactRelativeGapGrade18Coeff1 v) +
    (r^(2 : ℕ)*evenCompactRelativeGapGrade18Coeff2 v) : ℝ) : ℝ)

/-- Exact symbolic relative-shear identity at this entire gap degree. -/
theorem evenCompactRawGapGrade18_relative_eq (u v : ℝ) :
    evenCompactRawGapGrade18 u (u*(1+v/4)) = evenCompactRelativeGapGrade18 (u^(2 : ℕ)) v := by
  unfold evenCompactRawGapGrade18 evenCompactRelativeGapGrade18 evenCompactRelativeGapGrade18Coeff0 evenCompactRelativeGapGrade18Coeff1 evenCompactRelativeGapGrade18Coeff2
  ring1

end
end HTGeometry
