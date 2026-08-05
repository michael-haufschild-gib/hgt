import GaloisForLFunctions.HTGeometry.RationalShiftNoSolution

/-!
# The shift-inverse-square equation has the zero solution

The no-solution theorem rules out nonzero rational solutions of the shift-inverse-square equation.
The equation itself is not empty: the zero pair solves it, and so does every pair with zero
denominator.  So the no-go is a statement about a nonempty equation with a distinguished trivial
solution, not about an inconsistent one.
-/

open Polynomial

namespace GaloisForLFunctions

@[simp] theorem shiftOne_zero : shiftOne 0 = 0 := by
  rw [shiftOne, Polynomial.zero_comp]

/-- The zero denominator solves the shift-inverse-square equation, whatever the numerator. -/
theorem isShiftInvSqSolution_den_zero (p : ℂ[X]) : IsShiftInvSqSolution p 0 := by
  rw [IsShiftInvSqSolution]
  simp

/-- The zero pair solves the shift-inverse-square equation. -/
theorem isShiftInvSqSolution_zero : IsShiftInvSqSolution (0 : ℂ[X]) 0 :=
  isShiftInvSqSolution_den_zero 0

end GaloisForLFunctions
