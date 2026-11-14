import GaloisForLFunctions.HTGeometry.Polynomial.ChebyshevDifferential
import GaloisForLFunctions.HTGeometry.CavityInteractionCoefficients

/-!
# A quadratic energy law for cavity interaction coefficients

The second-kind Chebyshev representation of the interaction hierarchy
pairs with a first-kind mode in a scaled Pell identity. Dropping the
square of that mode gives a weighted bound on every interaction order.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial

/-- Exact homogeneous energy of every cavity interaction order. -/
theorem cavityInteractionCoeff_chebyshev_energy (η s d D : ℝ) (n : ℕ) :
    (η * d / 2 * (η * s) ^ n * (Chebyshev.T ℝ ((n : ℤ) + 1)).eval (-D * s)) ^ 2 +
      (1 - (D * s) ^ 2) * cavityInteractionCoeff η (s ^ 2) d D n ^ 2 =
        (η * d / 2) ^ 2 * (η * s) ^ (2 * n) := by
  rw [cavityInteractionCoeff_chebyshev]
  have h := congrArg (Polynomial.eval (-D * s)) (chebyshev_T_pell (R := ℝ) ((n : ℤ) + 1))
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_one, eval_X,
    add_sub_cancel_right] at h
  rw [mul_comm 2 n, pow_mul]
  linear_combination (η * d / 2 * (η * s) ^ n) ^ 2 * h

/-- The Pell identity bounds the weighted interaction strength without parameter exclusions. -/
theorem cavityInteractionCoeff_weighted_sq_le (η s d D : ℝ) (n : ℕ) :
    (1 - (D * s) ^ 2) * cavityInteractionCoeff η (s ^ 2) d D n ^ 2 ≤
      (η * d / 2) ^ 2 * (η * s) ^ (2 * n) := by
  have h := cavityInteractionCoeff_chebyshev_energy η s d D n
  rw [← h]
  exact le_add_of_nonneg_left (sq_nonneg _)

end GaloisForLFunctions.HTGeometry
