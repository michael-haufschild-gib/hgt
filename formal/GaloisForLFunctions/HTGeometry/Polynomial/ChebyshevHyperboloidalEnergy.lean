import GaloisForLFunctions.HTGeometry.Polynomial.ChebyshevDifferential
import GaloisForLFunctions.HTGeometry.QNMHyperboloidalPolynomial
import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy

/-!
# Chebyshev energy in wave profiles and quadratic response

The hyperboloidal derivative at zero frequency obeys an exact quadratic
identity. The reciprocal-quadratic response coefficients supply the
second-kind component of the same Pell equation.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {R : Type*} [CommRing R]

/-- Exact energy of a zero-frequency hyperboloidal Chebyshev profile. -/
theorem qnmHyperboloidalDx_chebyshev_energy (n : ℤ) :
    qnmHyperboloidalDx (0 : R) (Chebyshev.T R n) ^ 2 =
      (n : R[X]) ^ 2 * (1 - X ^ 2) * (1 - Chebyshev.T R n ^ 2) := by
  simp only [qnmHyperboloidalDx, C_0, zero_mul, sub_zero]
  linear_combination (X ^ 2 - 1) * chebyshev_T_differential_energy (R := R) n

/-- Frequency compensation recovers the same exact energy at every frequency. -/
theorem qnmHyperboloidalDx_compensated_energy (z : R) (n : ℤ) :
    (qnmHyperboloidalDx z (Chebyshev.T R n) + C z * X * Chebyshev.T R n) ^ 2 =
      (n : R[X]) ^ 2 * (1 - X ^ 2) * (1 - Chebyshev.T R n ^ 2) := by
  have heq : qnmHyperboloidalDx z (Chebyshev.T R n) + C z * X * Chebyshev.T R n =
      qnmHyperboloidalDx (0 : R) (Chebyshev.T R n) := by
    simp only [qnmHyperboloidalDx, sub_add_cancel, C_0, zero_mul, sub_zero]
  rw [heq, qnmHyperboloidalDx_chebyshev_energy]

/-- The quadratic-response coefficient and first-kind mode form a unit Pell pair. -/
theorem quadraticResponseCoeff_chebyshev_energy (x : R) (n : ℕ) :
    (Chebyshev.T R ((n : ℤ) + 1)).eval x ^ 2 +
      (1 - x ^ 2) * quadraticResponseCoeff (-(2 * x)) 1 n ^ 2 = 1 := by
  rw [quadraticResponseCoeff_eq_chebyshev]
  have h := congrArg (Polynomial.eval x) (chebyshev_T_pell (R := R) ((n : ℤ) + 1))
  simpa only [eval_add, eval_mul, eval_sub, eval_pow, eval_one, eval_X,
    add_sub_cancel_right] using h

/-- Damping multiplies the unit Pell energy by its exact homogeneous weight. -/
theorem quadraticResponseCoeff_damped_energy (x r : R) (n : ℕ) :
    (r ^ n * (Chebyshev.T R ((n : ℤ) + 1)).eval x) ^ 2 +
      (1 - x ^ 2) * quadraticResponseCoeff (-(2 * x * r)) (r ^ 2) n ^ 2 =
      r ^ (2 * n) := by
  rw [quadraticResponseCoeff_eq_scaled_chebyshev]
  have h := quadraticResponseCoeff_chebyshev_energy x n
  rw [quadraticResponseCoeff_eq_chebyshev] at h
  rw [mul_comm 2 n, pow_mul]
  linear_combination (r ^ n) ^ 2 * h

end GaloisForLFunctions.HTGeometry
