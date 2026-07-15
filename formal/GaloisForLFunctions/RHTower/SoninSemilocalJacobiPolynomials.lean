import GaloisForLFunctions.RHTower.SoninSemilocalGammaMoments
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiTransformDifferential

/-!
# The archimedean Jacobi polynomial family

This file constructs the actual real polynomial family selected by the Gamma measure's symmetric
three-term recurrence.  The positive recurrence coefficients fix the positive-leading-coefficient
normalization used by the semilocal Sonin source.
-/

noncomputable section

open Polynomial

namespace RHTower

/-- The archimedean Jacobi polynomial family, normalized by `p₀ = 1` and the source recurrence. -/
def semilocalArchimedeanJacobiPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (semilocalArchimedeanJacobiCoefficient 0)⁻¹ * X
  | n + 2 =>
      C (semilocalArchimedeanJacobiCoefficient (n + 1))⁻¹ *
        (X * semilocalArchimedeanJacobiPolynomial (n + 1) -
          C (semilocalArchimedeanJacobiCoefficient n) *
            semilocalArchimedeanJacobiPolynomial n)

@[simp]
theorem semilocalArchimedeanJacobiPolynomial_zero :
    semilocalArchimedeanJacobiPolynomial 0 = 1 := rfl

@[simp]
theorem semilocalArchimedeanJacobiPolynomial_one :
    semilocalArchimedeanJacobiPolynomial 1 =
      C (semilocalArchimedeanJacobiCoefficient 0)⁻¹ * X := rfl

theorem semilocalArchimedeanJacobiPolynomial_recurrence (n : ℕ) :
    X * semilocalArchimedeanJacobiPolynomial (n + 1) =
      C (semilocalArchimedeanJacobiCoefficient n) *
          semilocalArchimedeanJacobiPolynomial n +
        C (semilocalArchimedeanJacobiCoefficient (n + 1)) *
          semilocalArchimedeanJacobiPolynomial (n + 2) := by
  rw [semilocalArchimedeanJacobiPolynomial]
  have ha : semilocalArchimedeanJacobiCoefficient (n + 1) ≠ 0 :=
    (semilocalArchimedeanJacobiCoefficient_pos (n + 1)).ne'
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  ring

theorem semilocalArchimedeanJacobiPolynomial_eval_recurrence (n : ℕ) (s : ℝ) :
    s * (semilocalArchimedeanJacobiPolynomial (n + 1)).eval s =
      semilocalArchimedeanJacobiCoefficient n *
          (semilocalArchimedeanJacobiPolynomial n).eval s +
        semilocalArchimedeanJacobiCoefficient (n + 1) *
          (semilocalArchimedeanJacobiPolynomial (n + 2)).eval s := by
  have h := congrArg (Polynomial.eval s)
    (semilocalArchimedeanJacobiPolynomial_recurrence n)
  simpa using h

@[simp]
theorem semilocalArchimedeanJacobiPolynomial_eval_zero (s : ℝ) :
    (semilocalArchimedeanJacobiPolynomial 0).eval s = 1 := by
  simp

@[simp]
theorem semilocalArchimedeanJacobiPolynomial_eval_one (s : ℝ) :
    (semilocalArchimedeanJacobiPolynomial 1).eval s =
      (semilocalArchimedeanJacobiCoefficient 0)⁻¹ * s := by
  simp

end RHTower
