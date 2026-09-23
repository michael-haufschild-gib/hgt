import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

/-!
# QNMHyperboloidalPolynomial

The spatial derivative in Bizoń--Mach coordinates acts on a frequency profile
as (1-X²)∂X-zX. Its square and Chebyshev action are exact polynomial identities.
This supplies the squared coefficient in equations (12)--(13) and the spectral
basis of Al Sheikh--Jaramillo, arXiv:2607.25133.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable {R : Type*} [CommRing R]

def qnmHyperboloidalDx (z : R) (P : Polynomial R) : Polynomial R :=
  (1 - X ^ (2 : ℕ)) * P.derivative - C z * X * P

theorem qnmHyperboloidalDx_squared (z : R) (P : Polynomial R) :
    qnmHyperboloidalDx z (qnmHyperboloidalDx z P) =
      (1 - X ^ (2 : ℕ)) ^ (2 : ℕ) * P.derivative.derivative -
        2 * (C z + 1) * X * (1 - X ^ (2 : ℕ)) * P.derivative +
        (C z ^ (2 : ℕ) * X ^ (2 : ℕ) - C z * (1 - X ^ (2 : ℕ))) * P := by
  norm_num [qnmHyperboloidalDx, derivative_mul, derivative_sub, derivative_pow]
  simp only [Polynomial.C_ofNat]
  ring

theorem qnmHyperboloidalDx_right_endpoint (z : R) (P : Polynomial R) :
    (qnmHyperboloidalDx z P).eval 1 = -z * P.eval 1 := by
  simp [qnmHyperboloidalDx]

theorem qnmHyperboloidalDx_left_endpoint (z : R) (P : Polynomial R) :
    (qnmHyperboloidalDx z P).eval (-1) = z * P.eval (-1) := by
  simp [qnmHyperboloidalDx]

theorem qnmHyperboloidalDx_chebyshev (z : R) (n : ℤ) :
    qnmHyperboloidalDx z (Chebyshev.T R (n + 1)) =
      (n + 1 : Polynomial R) * Chebyshev.T R n -
        ((n + 1 : Polynomial R) + C z) * X * Chebyshev.T R (n + 1) := by
  rw [qnmHyperboloidalDx,
    Chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T]
  ring

theorem qnmHyperboloidalDx_squared_chebyshev (z : R) (n : ℤ) :
    qnmHyperboloidalDx z (qnmHyperboloidalDx z (Chebyshev.T R n)) =
      -(2 * C z + 1) * X * (1 - X ^ (2 : ℕ)) * (Chebyshev.T R n).derivative +
        (C z ^ (2 : ℕ) * X ^ (2 : ℕ) - ((n : Polynomial R) ^ (2 : ℕ) + C z) * (1 - X ^ (2 : ℕ))) * Chebyshev.T R n := by
  rw [qnmHyperboloidalDx_squared]
  have h := Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := R) n
  change (1 - X ^ (2 : ℕ)) * (Chebyshev.T R n).derivative.derivative =
    X * (Chebyshev.T R n).derivative - (n ^ (2 : ℕ) : Polynomial R) * Chebyshev.T R n at h
  calc
    _ = (1 - X ^ (2 : ℕ)) * ((1 - X ^ (2 : ℕ)) * (Chebyshev.T R n).derivative.derivative) -
        2 * (C z + 1) * X * (1 - X ^ (2 : ℕ)) * (Chebyshev.T R n).derivative +
        (C z ^ (2 : ℕ) * X ^ (2 : ℕ) - C z * (1 - X ^ (2 : ℕ))) * Chebyshev.T R n := by ring
    _ = _ := by rw [h]; ring

end GaloisForLFunctions.HTGeometry
