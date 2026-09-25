import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Exact relative-shear substitution at one modular gap degree -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Gap-degree 17 of the full corrected raw determinant, in fixed units. -/
def evenCompactRawGapGrade17 (u w : ℝ) : ℝ :=
  (((((2370080393613/549755813888000000000000000000000000 : ℝ) +
    (3552176063637/2199023255552000000000000000000000000 : ℝ)*w^(2 : ℕ) : ℝ) +
    ((93676004577/219902325555200000000000000000000000 : ℝ)*w^(4 : ℕ) +
    (2998431459/137438953472000000000000000000000000 : ℝ)*w^(6 : ℕ) : ℝ) : ℝ) +
    (((-744128427159/549755813888000000000000000000000000 : ℝ)*u^(1 : ℕ)*w^(1 : ℕ) +
    (367447344903/549755813888000000000000000000000000 : ℝ)*u^(1 : ℕ)*w^(3 : ℕ) : ℝ) +
    ((-1049333301/549755813888000000000000000000000000 : ℝ)*u^(1 : ℕ)*w^(5 : ℕ) +
    (1103083737057/2199023255552000000000000000000000000 : ℝ)*u^(2 : ℕ) : ℝ) : ℝ) : ℝ) +
    ((((-1275699168489/2199023255552000000000000000000000000 : ℝ)*u^(2 : ℕ)*w^(2 : ℕ) +
    (-55902623889/274877906944000000000000000000000000 : ℝ)*u^(2 : ℕ)*w^(4 : ℕ) : ℝ) +
    ((23206205169/219902325555200000000000000000000000 : ℝ)*u^(3 : ℕ)*w^(1 : ℕ) +
    (-25333541299/274877906944000000000000000000000000 : ℝ)*u^(3 : ℕ)*w^(3 : ℕ) : ℝ) : ℝ) +
    (((658206537643/6597069766656000000000000000000000000 : ℝ)*u^(4 : ℕ) +
    (-1959325621/12884901888000000000000000000000000 : ℝ)*u^(4 : ℕ)*w^(2 : ℕ) : ℝ) +
    ((-661568189027/9895604649984000000000000000000000000 : ℝ)*u^(5 : ℕ)*w^(1 : ℕ) +
    (-11909496781/1187472557998080000000000000000000000 : ℝ)*u^(6 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- Exact drift-degree 0 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade17Coeff0 (_v : ℝ) : ℝ :=
  (2370080393613/549755813888000000000000000000000000 : ℝ)

/-- Exact drift-degree 1 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade17Coeff1 (v : ℝ) : ℝ :=
  ((839373046029/1099511627776000000000000000000000000 : ℝ) +
    ((2063919209319/4398046511104000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (3552176063637/35184372088832000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ)

/-- Exact drift-degree 2 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade17Coeff2 (v : ℝ) : ℝ :=
  (((148341983231/206158430208000000000000000000000000 : ℝ) +
    (1459268009157/2199023255552000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((8754229244967/35184372088832000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    ((1304207390673/35184372088832000000000000000000000000 : ℝ)*v^(3 : ℕ) +
    (93676004577/56294995342131200000000000000000000000 : ℝ)*v^(4 : ℕ) : ℝ) : ℝ) : ℝ)

/-- Exact drift-degree 3 coefficient after relative-shear substitution. -/
def evenCompactRelativeGapGrade17Coeff3 (v : ℝ) : ℝ :=
  (((-3744809215201/7421703487488000000000000000000000000 : ℝ) +
    ((-13256210249993/39582418599936000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (-552763554821/6597069766656000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ) +
    (((-26850689/3518437208883200000000000000000000 : ℝ)*v^(3 : ℕ) +
    (62853973257/140737488355328000000000000000000000000 : ℝ)*v^(4 : ℕ) : ℝ) +
    ((14182604343/112589990684262400000000000000000000000 : ℝ)*v^(5 : ℕ) +
    (2998431459/562949953421312000000000000000000000000 : ℝ)*v^(6 : ℕ) : ℝ) : ℝ) : ℝ)

/-- The relative-shear polynomial retains drift grading. -/
def evenCompactRelativeGapGrade17 (r v : ℝ) : ℝ :=
  ((evenCompactRelativeGapGrade17Coeff0 v +
    (r^(1 : ℕ)*evenCompactRelativeGapGrade17Coeff1 v) : ℝ) +
    ((r^(2 : ℕ)*evenCompactRelativeGapGrade17Coeff2 v) +
    (r^(3 : ℕ)*evenCompactRelativeGapGrade17Coeff3 v) : ℝ) : ℝ)

/-- Exact symbolic relative-shear identity at this entire gap degree. -/
theorem evenCompactRawGapGrade17_relative_eq (u v : ℝ) :
    evenCompactRawGapGrade17 u (u*(1+v/4)) = evenCompactRelativeGapGrade17 (u^2) v := by
  unfold evenCompactRawGapGrade17 evenCompactRelativeGapGrade17 evenCompactRelativeGapGrade17Coeff0 evenCompactRelativeGapGrade17Coeff1 evenCompactRelativeGapGrade17Coeff2 evenCompactRelativeGapGrade17Coeff3
  ring1

end
end HTGeometry
