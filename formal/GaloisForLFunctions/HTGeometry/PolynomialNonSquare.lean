import GaloisForLFunctions.HTGeometry.SquareClassPrime
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# A polynomial times a variable it is not divisible by is not a square

A variable is prime in a polynomial ring, so a polynomial not divisible by it, multiplied by it, is
divisible by that prime exactly once and therefore is not a square in the field of fractions.

Applied to the discriminant against the constant coefficient this is the square-class input of the
even Kummer case.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- **A polynomial times a variable not dividing it is a nonsquare.** -/
theorem not_isSquare_mul_X_of_not_dvd {P : MvPolynomial σ K} {i : σ}
    (h : ¬ (MvPolynomial.X i : MvPolynomial σ K) ∣ P) :
    ¬ IsSquare (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
      (P * MvPolynomial.X i)) :=
  not_isSquare_of_prime_dvd_once (MvPolynomial.X_prime) (mul_comm P (MvPolynomial.X i)) h

end GaloisForLFunctions.HTGeometry
