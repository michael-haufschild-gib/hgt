import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic.LinearCombination

/-!
# Chebyshev differential identities

The recurrence invariant for the second-kind polynomials gives the Pell
identity for both normalizations. Differentiation converts it into an exact
quadratic energy law. Affine pullback retains this law without division, so
it also applies to degenerate changes of variable and in positive characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {R : Type*} [CommRing R]

/-- The normalized first-kind polynomial and its second-kind companion solve a Pell equation. -/
theorem chebyshev_C_pell (n : ℤ) :
    Chebyshev.C R n ^ 2 - (X ^ 2 - 4) * Chebyshev.S R (n - 1) ^ 2 = 4 := by
  have h := Chebyshev.S_sq_add_S_sq R (n - 1)
  rw [sub_add_cancel] at h
  rw [Chebyshev.C_eq_S_sub_X_mul_S]
  linear_combination 4 * h

/-- The derivative of the monic normalization has no powers of two in its coefficients. -/
theorem chebyshev_C_derivative (n : ℕ) :
    (Chebyshev.C R (n : ℤ)).derivative =
      (n : R[X]) * Chebyshev.S R ((n : ℤ) - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [Nat.cast_zero, Chebyshev.C_zero, derivative_ofNat, zero_mul]
  | one => simp
  | more n h0 h1 =>
    have hs := Chebyshev.S_add_one R (n : ℤ)
    have hc := Chebyshev.C_eq_S_sub_X_mul_S R ((n : ℤ) + 1)
    simp only [add_sub_cancel_right] at hc
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_two, add_sub_cancel_right] at h1 ⊢
    rw [Chebyshev.C_add_two, derivative_sub, derivative_mul,
      derivative_X, one_mul, h0, h1]
    rw [show (n : ℤ) + 2 - 1 = n + 1 by ring]
    linear_combination hc - (n : R[X]) * hs

/-- The monic Chebyshev differential energy identity over any commutative ring. -/
theorem chebyshev_C_differential_energy (n : ℕ) :
    (X ^ 2 - 4) * (Chebyshev.C R (n : ℤ)).derivative ^ 2 =
      (n : R[X]) ^ 2 * (Chebyshev.C R (n : ℤ) ^ 2 - 4) := by
  rw [chebyshev_C_derivative]
  linear_combination -(n : R[X]) ^ 2 * chebyshev_C_pell (R := R) (n : ℤ)

/-- The same differential identity in the corpus's Dickson normalization. -/
theorem dickson_differential_energy (n : ℕ) :
    (X ^ 2 - 4) * (dickson 1 (1 : R) n).derivative ^ 2 =
      (n : R[X]) ^ 2 * (dickson 1 (1 : R) n ^ 2 - 4) := by
  rw [dickson_one_one_eq_chebyshev_C]
  exact chebyshev_C_differential_energy n

/-- The classical normalization has unit Pell constant. -/
theorem chebyshev_T_pell (n : ℤ) :
    Chebyshev.T R n ^ 2 + (1 - X ^ 2) * Chebyshev.U R (n - 1) ^ 2 = 1 := by
  have h := congrArg (fun P : R[X] => P.comp (2 * X))
    (Chebyshev.S_sq_add_S_sq R (n - 1))
  simp only [add_comp, sub_comp, pow_comp, mul_comp, X_comp, one_comp,
    Chebyshev.S_comp_two_mul_X, sub_add_cancel] at h
  rw [Chebyshev.T_eq_U_sub_X_mul_U]
  linear_combination h

/-- Differential energy of the classical Chebyshev polynomial. -/
theorem chebyshev_T_differential_energy (n : ℤ) :
    (X ^ 2 - 1) * (Chebyshev.T R n).derivative ^ 2 =
      (n : R[X]) ^ 2 * (Chebyshev.T R n ^ 2 - 1) := by
  rw [Chebyshev.T_derivative_eq_U]
  linear_combination -(n : R[X]) ^ 2 * chebyshev_T_pell (R := R) n

/-- Affine changes of variable preserve the differential energy law without division. -/
theorem chebyshev_affine_differential_energy (n : ℤ) (a b : R) :
    ((C a * X + C b) ^ 2 - 1) *
        ((Chebyshev.T R n).comp (C a * X + C b)).derivative ^ 2 =
      C a ^ 2 * (n : R[X]) ^ 2 *
        (((Chebyshev.T R n).comp (C a * X + C b)) ^ 2 - 1) := by
  have h := congrArg (fun P : R[X] => P.comp (C a * X + C b))
    (chebyshev_T_differential_energy (R := R) n)
  simp only [mul_comp, sub_comp, pow_comp, X_comp, one_comp, intCast_comp] at h
  simp only [derivative_comp, derivative_add, derivative_mul, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, add_zero]
  linear_combination C a ^ 2 * h

/-- The affine pullback also satisfies the second-order Chebyshev equation. -/
theorem chebyshev_affine_differential_equation (n : ℤ) (a b : R) :
    ((C a * X + C b) ^ 2 - 1) *
        ((Chebyshev.T R n).comp (C a * X + C b)).derivative.derivative +
      C a * (C a * X + C b) *
        ((Chebyshev.T R n).comp (C a * X + C b)).derivative =
      C a ^ 2 * (n : R[X]) ^ 2 * (Chebyshev.T R n).comp (C a * X + C b) := by
  have h := congrArg (fun P : R[X] => P.comp (C a * X + C b))
    (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := R) n)
  simp only [mul_comp, sub_comp, pow_comp, X_comp, one_comp, intCast_comp,
    Function.iterate_succ_apply, Function.iterate_zero_apply] at h
  simp only [derivative_comp, derivative_add, derivative_mul, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, add_zero]
  linear_combination -C a ^ 2 * h

end GaloisForLFunctions.HTGeometry
