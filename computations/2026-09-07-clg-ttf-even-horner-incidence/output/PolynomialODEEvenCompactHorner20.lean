import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade20
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactHorner21
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactUnitCoordinates

/-! # A single linear-factor Horner step for the compact determinant -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Drift-degree 0 in this exact Horner remainder. -/
def evenCompactHorner20Coeff0 (_t _v : ℝ) : ℝ :=
  (-913113/4503599627370496000000000000000000 : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner20Coeff0_eq (t v : ℝ) :
    evenCompactHorner20Coeff0 t v = (evenCompactRelativeGapGrade20Coeff0 v)+
      (191/10+t/10)*((0 : ℝ))+(-12/5+(16/15)*t)*((0 : ℝ)) := by
  unfold evenCompactHorner20Coeff0 evenCompactRelativeGapGrade20Coeff0
  ring1

/-- The exact Horner polynomial retains its drift grading. -/
def evenCompactHorner20 (_r t v : ℝ) : ℝ :=
  evenCompactHorner20Coeff0 t v

/-- Assemble the checked coefficient identities without expanding their polynomials. -/
theorem evenCompactHorner20_step (r t v : ℝ) :
    evenCompactHorner20 r t v = evenCompactRelativeGapGrade20 r v+
      evenCompactUnitGap r t*evenCompactHorner21 r t v := by
  unfold evenCompactHorner20 evenCompactHorner21
  rw [evenCompactHorner20Coeff0_eq]
  unfold evenCompactRelativeGapGrade20 evenCompactUnitGap
  ring1

end
end HTGeometry
