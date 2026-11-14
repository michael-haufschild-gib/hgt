import GaloisForLFunctions.KodairaParshinAbc.Periods.SymmetricSquare
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Symmetric-square equations for Chebyshev transfer polynomials

Both Chebyshev families used in arithmetic transfer recurrences admit the
same third-order lift as a rank-two Picard--Fuchs equation. The identities
are integral, uniform in the index, and retain both singular endpoints.
-/

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open Polynomial Polynomial.Chebyshev KodairaParshinAbc.Periods

variable {R : Type*} [CommRing R]

/-- The first-kind transfer polynomial has an integral symmetric-square equation. -/
theorem chebyshevT_squared_equation (n : ℤ) :
    symmetricSquare (1 - X ^ 2) (-X) ((n : R[X]) ^ 2) (T R n ^ 2) = 0 := by
  have h₀ := one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := R) n
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h₀
  have h : secondOrder (1 - X ^ 2) (-X) ((n : R[X]) ^ 2) (T R n) = 0 := by
    rw [secondOrder, h₀]
    ring
  rw [symmetricSquare_square, h, derivative_zero, mul_zero, mul_zero, add_zero]

/-- The second-kind Hecke polynomial has an integral symmetric-square equation. -/
theorem chebyshevU_squared_equation (n : ℤ) :
    symmetricSquare (1 - X ^ 2) (-3 * X) (((n : R[X]) + 2) * (n : R[X])) (U R n ^ 2) = 0 := by
  have h₀ := one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (R := R) n
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h₀
  have h : secondOrder (1 - X ^ 2) (-3 * X) (((n : R[X]) + 2) * (n : R[X])) (U R n) = 0 := by
    rw [secondOrder, h₀]
    ring
  rw [symmetricSquare_square, h, derivative_zero, mul_zero, mul_zero, add_zero]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.chebyshevT_squared_equation
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.chebyshevU_squared_equation
