import GaloisForLFunctions.KodairaParshinAbc.Periods.SymmetricSquare
import GaloisForLFunctions.KodairaParshinAbc.Legendre.DeuringPolynomials

/-!
# Symmetric-square equations for the binomial-square periods

The terminating Gauss equation lifts to an integral third-order equation for
the square of every binomial-square polynomial. Its reduction modulo `2n+1`
gives the symmetric square of the Legendre Picard--Fuchs equation, including
composite odd moduli. No interpretation as a geometric K3 period is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Legendre

open Polynomial Periods

variable {R : Type*} [CommRing R]

/-- The complete terminating Gauss family satisfies its symmetric-square equation. -/
theorem binomialSquare_symmetricSquare (n : ℕ) :
    symmetricSquare (X * (1 - X)) (1 + C (2 * (n : R) - 1) * X)
      (-C ((n : R) ^ 2)) ((binomialSquare n : R[X]) ^ 2) = 0 := by
  have h : secondOrder (X * (1 - X)) (1 + C (2 * (n : R) - 1) * X)
      (-C ((n : R) ^ 2)) (binomialSquare n) = 0 := by
    simpa only [secondOrder, neg_mul, sub_eq_add_neg] using binomialSquare_gauss (R := R) n
  rw [symmetricSquare_square, h, derivative_zero, mul_zero, mul_zero, add_zero]

/-- The Legendre symmetric square survives reduction at every odd modulus. -/
theorem deuring_symmetricSquare (n : ℕ) :
    symmetricSquare (4 * X * (1 - X)) (4 * (1 - 2 * X)) (-1)
      ((binomialSquare n : (ZMod (2 * n + 1))[X]) ^ 2) = 0 := by
  have h : secondOrder (4 * X * (1 - X)) (4 * (1 - 2 * X)) (-1)
      (binomialSquare n : (ZMod (2 * n + 1))[X]) = 0 := by
    simpa only [secondOrder, neg_one_mul, sub_eq_add_neg] using binomialSquare_picardFuchs n
  rw [symmetricSquare_square, h, derivative_zero, mul_zero, mul_zero, add_zero]

/-- The derivative of the period ratio is compatible with the integral symmetric square. -/
theorem binomialSquare_product_wronskian (n : ℕ) (g : R[X]) :
    wronskian ((binomialSquare n : R[X]) ^ 2) (binomialSquare n * g) =
      binomialSquare n ^ 2 * wronskian (binomialSquare n) g :=
  wronskian_square_product _ _

end GaloisForLFunctions.KodairaParshinAbc.Legendre
