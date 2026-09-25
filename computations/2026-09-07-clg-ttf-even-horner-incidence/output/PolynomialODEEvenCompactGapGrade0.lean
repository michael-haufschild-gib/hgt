import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Exact relative-shear substitution at one modular gap degree -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Gap-degree 0 of the full corrected raw determinant, in fixed units. -/
def evenCompactRawGapGrade0 (u _w : ℝ) : ℝ :=
  (((((1414448154622251/389120000000000000000000 : ℝ) +
    (-1266282599090733/194560000000000000000000 : ℝ)*u^(2 : ℕ) : ℝ) +
    ((10923511096323/2048000000000000000000 : ℝ)*u^(4 : ℕ) +
    ((-1034745712549983/389120000000000000000000 : ℝ)*u^(6 : ℕ) +
    (179884821330837/199229440000000000000000 : ℝ)*u^(8 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((-344304864061641/1556480000000000000000000 : ℝ)*u^(10 : ℕ) +
    (377071503890977/9338880000000000000000000 : ℝ)*u^(12 : ℕ) : ℝ) +
    ((-234672628089613/42024960000000000000000000 : ℝ)*u^(14 : ℕ) +
    ((98972955946949/168099840000000000000000000 : ℝ)*u^(16 : ℕ) +
    (-17850931794227/378224640000000000000000000 : ℝ)*u^(18 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) +
    ((((523082322493661/183817175040000000000000000000 : ℝ)*u^(20 : ℕ) +
    (-35049752294053/275725762560000000000000000000 : ℝ)*u^(22 : ℕ) : ℝ) +
    ((251144676417019/59556764712960000000000000000000 : ℝ)*u^(24 : ℕ) +
    ((-871754576987/7444595589120000000000000000000 : ℝ)*u^(26 : ℕ) +
    (27828769871/7052774768640000000000000000000 : ℝ)*u^(28 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((-206599141/1175462461440000000000000000000 : ℝ)*u^(30 : ℕ) +
    ((19917569/2821109907456000000000000000000 : ℝ)*u^(32 : ℕ) +
    (-20246947/95212459376640000000000000000000 : ℝ)*u^(34 : ℕ) : ℝ) : ℝ) +
    ((860587/190424918753280000000000000000000 : ℝ)*u^(36 : ℕ) +
    ((-51793/856912134389760000000000000000000 : ℝ)*u^(38 : ℕ) +
    (141659/370186042056376320000000000000000000 : ℝ)*u^(40 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- Exact drift-degree 0 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff0 (_v : ℝ) : ℝ :=
  (1414448154622251/389120000000000000000000 : ℝ)

/-- Exact drift-degree 1 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff1 (_v : ℝ) : ℝ :=
  (-1266282599090733/194560000000000000000000 : ℝ)

/-- Exact drift-degree 2 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff2 (_v : ℝ) : ℝ :=
  (10923511096323/2048000000000000000000 : ℝ)

/-- Exact drift-degree 3 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff3 (_v : ℝ) : ℝ :=
  (-1034745712549983/389120000000000000000000 : ℝ)

/-- Exact drift-degree 4 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff4 (_v : ℝ) : ℝ :=
  (179884821330837/199229440000000000000000 : ℝ)

/-- Exact drift-degree 5 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff5 (_v : ℝ) : ℝ :=
  (-344304864061641/1556480000000000000000000 : ℝ)

/-- Exact drift-degree 6 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff6 (_v : ℝ) : ℝ :=
  (377071503890977/9338880000000000000000000 : ℝ)

/-- Exact drift-degree 7 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff7 (_v : ℝ) : ℝ :=
  (-234672628089613/42024960000000000000000000 : ℝ)

/-- Exact drift-degree 8 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff8 (_v : ℝ) : ℝ :=
  (98972955946949/168099840000000000000000000 : ℝ)

/-- Exact drift-degree 9 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff9 (_v : ℝ) : ℝ :=
  (-17850931794227/378224640000000000000000000 : ℝ)

/-- Exact drift-degree 10 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff10 (_v : ℝ) : ℝ :=
  (523082322493661/183817175040000000000000000000 : ℝ)

/-- Exact drift-degree 11 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff11 (_v : ℝ) : ℝ :=
  (-35049752294053/275725762560000000000000000000 : ℝ)

/-- Exact drift-degree 12 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff12 (_v : ℝ) : ℝ :=
  (251144676417019/59556764712960000000000000000000 : ℝ)

/-- Exact drift-degree 13 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff13 (_v : ℝ) : ℝ :=
  (-871754576987/7444595589120000000000000000000 : ℝ)

/-- Exact drift-degree 14 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff14 (_v : ℝ) : ℝ :=
  (27828769871/7052774768640000000000000000000 : ℝ)

/-- Exact drift-degree 15 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff15 (_v : ℝ) : ℝ :=
  (-206599141/1175462461440000000000000000000 : ℝ)

/-- Exact drift-degree 16 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff16 (_v : ℝ) : ℝ :=
  (19917569/2821109907456000000000000000000 : ℝ)

/-- Exact drift-degree 17 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff17 (_v : ℝ) : ℝ :=
  (-20246947/95212459376640000000000000000000 : ℝ)

/-- Exact drift-degree 18 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff18 (_v : ℝ) : ℝ :=
  (860587/190424918753280000000000000000000 : ℝ)

/-- Exact drift-degree 19 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff19 (_v : ℝ) : ℝ :=
  (-51793/856912134389760000000000000000000 : ℝ)

/-- Exact drift-degree 20 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade0Coeff20 (_v : ℝ) : ℝ :=
  (141659/370186042056376320000000000000000000 : ℝ)

/-- The relative-shear polynomial retains drift grading. -/
def evenCompactRelativeGapGrade0 (r v : ℝ) : ℝ :=
  ((((evenCompactRelativeGapGrade0Coeff0 v +
    (r^(1 : ℕ)*evenCompactRelativeGapGrade0Coeff1 v) : ℝ) +
    ((r^(2 : ℕ)*evenCompactRelativeGapGrade0Coeff2 v) +
    ((r^(3 : ℕ)*evenCompactRelativeGapGrade0Coeff3 v) +
    (r^(4 : ℕ)*evenCompactRelativeGapGrade0Coeff4 v) : ℝ) : ℝ) : ℝ) +
    (((r^(5 : ℕ)*evenCompactRelativeGapGrade0Coeff5 v) +
    (r^(6 : ℕ)*evenCompactRelativeGapGrade0Coeff6 v) : ℝ) +
    ((r^(7 : ℕ)*evenCompactRelativeGapGrade0Coeff7 v) +
    ((r^(8 : ℕ)*evenCompactRelativeGapGrade0Coeff8 v) +
    (r^(9 : ℕ)*evenCompactRelativeGapGrade0Coeff9 v) : ℝ) : ℝ) : ℝ) : ℝ) +
    ((((r^(10 : ℕ)*evenCompactRelativeGapGrade0Coeff10 v) +
    (r^(11 : ℕ)*evenCompactRelativeGapGrade0Coeff11 v) : ℝ) +
    ((r^(12 : ℕ)*evenCompactRelativeGapGrade0Coeff12 v) +
    ((r^(13 : ℕ)*evenCompactRelativeGapGrade0Coeff13 v) +
    (r^(14 : ℕ)*evenCompactRelativeGapGrade0Coeff14 v) : ℝ) : ℝ) : ℝ) +
    (((r^(15 : ℕ)*evenCompactRelativeGapGrade0Coeff15 v) +
    ((r^(16 : ℕ)*evenCompactRelativeGapGrade0Coeff16 v) +
    (r^(17 : ℕ)*evenCompactRelativeGapGrade0Coeff17 v) : ℝ) : ℝ) +
    ((r^(18 : ℕ)*evenCompactRelativeGapGrade0Coeff18 v) +
    ((r^(19 : ℕ)*evenCompactRelativeGapGrade0Coeff19 v) +
    (r^(20 : ℕ)*evenCompactRelativeGapGrade0Coeff20 v) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- Exact symbolic relative-shear identity at this entire gap degree. -/
theorem evenCompactRawGapGrade0_relative_eq (u v : ℝ) :
    evenCompactRawGapGrade0 u (u*(1+v/4)) = evenCompactRelativeGapGrade0 (u^2) v := by
  unfold evenCompactRawGapGrade0 evenCompactRelativeGapGrade0 evenCompactRelativeGapGrade0Coeff0 evenCompactRelativeGapGrade0Coeff1 evenCompactRelativeGapGrade0Coeff2 evenCompactRelativeGapGrade0Coeff3 evenCompactRelativeGapGrade0Coeff4 evenCompactRelativeGapGrade0Coeff5 evenCompactRelativeGapGrade0Coeff6 evenCompactRelativeGapGrade0Coeff7 evenCompactRelativeGapGrade0Coeff8 evenCompactRelativeGapGrade0Coeff9 evenCompactRelativeGapGrade0Coeff10 evenCompactRelativeGapGrade0Coeff11 evenCompactRelativeGapGrade0Coeff12 evenCompactRelativeGapGrade0Coeff13 evenCompactRelativeGapGrade0Coeff14 evenCompactRelativeGapGrade0Coeff15 evenCompactRelativeGapGrade0Coeff16 evenCompactRelativeGapGrade0Coeff17 evenCompactRelativeGapGrade0Coeff18 evenCompactRelativeGapGrade0Coeff19 evenCompactRelativeGapGrade0Coeff20
  ring1

end
end HTGeometry
