import GaloisForLFunctions.HTGeometry.Polynomial.ChebyshevDifferential
import GaloisForLFunctions.RHTower.LiReciprocalKernelCoefficientSign

/-!
# Differential energy of the reciprocal Li kernel

The Chebyshev Pell identity transports through the reciprocal seam to a
quadratic law relating the kernel and its derivative. Clearing denominators
makes the identity valid on the entire real line, including the pole.
-/

noncomputable section
namespace RHTower
open Polynomial

/-- Global denominator-cleared energy law for the reciprocal Li kernel. -/
theorem liReciprocalKernel_differential_energy (n : ℕ) (y : ℝ) :
    y * (4 + y) ^ 4 * deriv (liReciprocalKernel n) y ^ 2 =
      4 * (n : ℝ) ^ 2 * (4 + y) ^ 2 *
        liReciprocalKernel n y * (4 - liReciprocalKernel n y) := by
  by_cases hy : 4 + y = 0
  · simp only [hy, zero_pow (by omega : (4 : ℕ) ≠ 0),
      zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, zero_mul]
  · rw [deriv_liReciprocalKernel n hy]
    have h := congrArg (Polynomial.eval (liReciprocalSeam y))
      (GaloisForLFunctions.HTGeometry.chebyshev_T_differential_energy (R := ℝ) (n : ℤ))
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one,
      Int.cast_natCast, eval_natCast] at h
    change (((4 - y) / (4 + y)) ^ 2 - 1) *
      (Chebyshev.T ℝ (n : ℤ)).derivative.eval (liReciprocalSeam y) ^ 2 = _ at h
    field_simp [hy] at h
    simp only [liReciprocalKernelDerivFormula, liReciprocalKernel]
    field_simp [hy]
    linear_combination -8 * h

end RHTower
