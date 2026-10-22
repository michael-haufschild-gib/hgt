import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade18
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactHorner19
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactUnitCoordinates

/-! # A single linear-factor Horner step for the compact determinant -/
namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Drift-degree 0 in this exact Horner remainder. -/
def evenCompactHorner18Coeff0 (t _v : ℝ) : ℝ :=
  ((-27405471128481/281474976710656000000000000000000000000 : ℝ) +
    ((-24281090847/28147497671065600000000000000000000000 : ℝ)*t^(1 : ℕ) +
    (-913113/450359962737049600000000000000000000 : ℝ)*t^(2 : ℕ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner18Coeff0_eq (t v : ℝ) :
    evenCompactHorner18Coeff0 t v = (evenCompactRelativeGapGrade18Coeff0 v)+
      (191/10+t/10)*(evenCompactHorner19Coeff0 t v)+(-12/5+(16/15)*t)*((0 : ℝ)) := by
  unfold evenCompactHorner18Coeff0 evenCompactRelativeGapGrade18Coeff0 evenCompactHorner19Coeff0
  ring1

/-- Drift-degree 1 in this exact Horner remainder. -/
def evenCompactHorner18Coeff1 (t v : ℝ) : ℝ :=
  (((-285569316771/4398046511104000000000000000000000000 : ℝ) +
    ((-38235941649/4398046511104000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (1755871819173/562949953421312000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ) +
    (((-2125129173/219902325555200000000000000000000000 : ℝ)*t^(1 : ℕ) +
    (-234003879/1759218604441600000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((-579868821/112589990684262400000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (-304371/7036874417766400000000000000000000 : ℝ)*t^(2 : ℕ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner18Coeff1_eq (t v : ℝ) :
    evenCompactHorner18Coeff1 t v = (evenCompactRelativeGapGrade18Coeff1 v)+
      (191/10+t/10)*(evenCompactHorner19Coeff1 t v)+(-12/5+(16/15)*t)*(evenCompactHorner19Coeff0 t v) := by
  unfold evenCompactHorner18Coeff1 evenCompactRelativeGapGrade18Coeff1 evenCompactHorner19Coeff1 evenCompactHorner19Coeff0
  ring1

/-- Drift-degree 2 in this exact Horner remainder. -/
def evenCompactHorner18Coeff2 (t v : ℝ) : ℝ :=
  ((((-1476499706663/26388279066624000000000000000000000000 : ℝ) +
    (-7669053999/274877906944000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((-615327712209/140737488355328000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    (-2126961279/17592186044416000000000000000000000000 : ℝ)*v^(3 : ℕ) : ℝ) : ℝ) +
    (((83499748533/4503599627370496000000000000000000000000 : ℝ)*v^(4 : ℕ) +
    (-135606581/27487790694400000000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) +
    ((-78001293/54975581388800000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
    ((-193289607/3518437208883200000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (-101457/439804651110400000000000000000000 : ℝ)*t^(2 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner18Coeff2_eq (t v : ℝ) :
    evenCompactHorner18Coeff2 t v = (evenCompactRelativeGapGrade18Coeff2 v)+
      (191/10+t/10)*((0 : ℝ))+(-12/5+(16/15)*t)*(evenCompactHorner19Coeff1 t v) := by
  unfold evenCompactHorner18Coeff2 evenCompactRelativeGapGrade18Coeff2 evenCompactHorner19Coeff1
  ring1

/-- The exact Horner polynomial retains its drift grading. -/
def evenCompactHorner18 (r t v : ℝ) : ℝ :=
  (evenCompactHorner18Coeff0 t v +
    ((r^(1 : ℕ)*evenCompactHorner18Coeff1 t v) +
    (r^(2 : ℕ)*evenCompactHorner18Coeff2 t v) : ℝ) : ℝ)

/-- Assemble the checked coefficient identities without expanding their polynomials. -/
theorem evenCompactHorner18_step (r t v : ℝ) :
    evenCompactHorner18 r t v = evenCompactRelativeGapGrade18 r v+
      evenCompactUnitGap r t*evenCompactHorner19 r t v := by
  unfold evenCompactHorner18 evenCompactHorner19
  rw [evenCompactHorner18Coeff0_eq, evenCompactHorner18Coeff1_eq, evenCompactHorner18Coeff2_eq]
  unfold evenCompactRelativeGapGrade18 evenCompactUnitGap
  ring1

end
end HTGeometry
