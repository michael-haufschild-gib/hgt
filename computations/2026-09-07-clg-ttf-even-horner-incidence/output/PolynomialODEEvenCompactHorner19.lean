import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapGrade19
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactHorner20
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates

/-! # A single linear-factor Horner step for the compact determinant -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Drift-degree 0 in this exact Horner remainder. -/
def evenCompactHorner19Coeff0 (t _v : ℝ) : ℝ :=
  ((-26761608819/5629499534213120000000000000000000000 : ℝ) +
    (-913113/45035996273704960000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner19Coeff0_eq (t v : ℝ) :
    evenCompactHorner19Coeff0 t v = (evenCompactRelativeGapGrade19Coeff0 v)+
      (191/10+t/10)*(evenCompactHorner20Coeff0 t v)+(-12/5+(16/15)*t)*((0 : ℝ)) := by
  unfold evenCompactHorner19Coeff0 evenCompactRelativeGapGrade19Coeff0 evenCompactHorner20Coeff0
  ring1

/-- Drift-degree 1 in this exact Horner remainder. -/
def evenCompactHorner19Coeff1 (t v : ℝ) : ℝ :=
  (((-3596975319/703687441776640000000000000000000000 : ℝ) +
    (-234003879/175921860444160000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((-579868821/11258999068426240000000000000000000000 : ℝ)*v^(2 : ℕ) +
    (-304371/1407374883553280000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner19Coeff1_eq (t v : ℝ) :
    evenCompactHorner19Coeff1 t v = (evenCompactRelativeGapGrade19Coeff1 v)+
      (191/10+t/10)*((0 : ℝ))+(-12/5+(16/15)*t)*(evenCompactHorner20Coeff0 t v) := by
  unfold evenCompactHorner19Coeff1 evenCompactRelativeGapGrade19Coeff1 evenCompactHorner20Coeff0
  ring1

/-- The exact Horner polynomial retains its drift grading. -/
def evenCompactHorner19 (r t v : ℝ) : ℝ :=
  (evenCompactHorner19Coeff0 t v +
    (r^(1 : ℕ)*evenCompactHorner19Coeff1 t v) : ℝ)

/-- Assemble the checked coefficient identities without expanding their polynomials. -/
theorem evenCompactHorner19_step (r t v : ℝ) :
    evenCompactHorner19 r t v = evenCompactRelativeGapGrade19 r v+
      evenCompactUnitGap r t*evenCompactHorner20 r t v := by
  unfold evenCompactHorner19 evenCompactHorner20
  rw [evenCompactHorner19Coeff0_eq, evenCompactHorner19Coeff1_eq]
  unfold evenCompactRelativeGapGrade19 evenCompactUnitGap
  ring1

end
end HTGeometry
