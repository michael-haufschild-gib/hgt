import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.Tactic

/-!
# The second-kind recurrence with a free coefficient

The recurrence used for imaginary-root polynomials in the Kronecker quantum
cluster algebra has a commuting coefficient. Its commutative polynomial model
gives a Cassini identity, addition law, and a parameter-dependent Pell equation.
The latter extends the normalized Chebyshev differential energy law.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial
variable {R : Type*} [CommRing R]

/-- Consecutive second-kind polynomials have a pure-power Cassini defect. -/
theorem dickson_second_cassini (a : R) (n : ℕ) :
    dickson 2 a (n + 1) ^ 2 - dickson 2 a n * dickson 2 a (n + 2) =
      C a ^ (n + 1) := by
  induction n with
  | zero => norm_num [dickson_zero, dickson_one, dickson_add_two]; ring
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 1) + 2 by omega, dickson_add_two]
    simp only [show n + 1 + 1 = n + 2 by omega, dickson_add_two] at ih ⊢
    rw [pow_succ (C a) (n + 1)]
    linear_combination C a * ih

/-- The addition formula keeps the recurrence coefficient, including zero. -/
theorem dickson_second_addition (a : R) (m n : ℕ) :
    dickson 2 a (m + n + 2) =
      dickson 2 a (m + 1) * dickson 2 a (n + 1) -
        C a * dickson 2 a m * dickson 2 a n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [dickson_zero, dickson_one, dickson_add_two]; ring
  | one =>
    rw [show m + 1 + 2 = (m + 1) + 2 by omega, dickson_add_two,
      dickson_add_two, dickson_add_two]
    norm_num [dickson_zero, dickson_one]
    ring
  | more n h0 h1 =>
    rw [show m + (n + 2) + 2 = (m + n + 2) + 2 by omega,
      dickson_add_two, show m + n + 2 + 1 = m + (n + 1) + 2 by omega,
      h0, h1, show n + 2 + 1 = (n + 1) + 2 by omega,
      dickson_add_two, dickson_add_two]
    simp only [show n + 1 + 1 = n + 2 by omega, dickson_add_two]
    ring

/-- The first kind is the trace companion of the second kind. -/
theorem dickson_first_eq_second (a : R) (n : ℕ) :
    dickson 1 a (n + 1) = 2 * dickson 2 a (n + 1) - X * dickson 2 a n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [dickson_zero, dickson_one]; ring
  | one => norm_num [dickson_zero, dickson_one, dickson_add_two]; ring
  | more n h0 h1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, dickson_add_two,
      h0, h1, dickson_add_two, dickson_add_two]
    simp only [show n + 1 + 1 = n + 2 by omega, dickson_add_two]
    ring

/-- The free recurrence coefficient becomes the power on the Pell right side. -/
theorem dickson_parameter_pell (a : R) (n : ℕ) :
    dickson 1 a (n + 1) ^ 2 - (X ^ 2 - 4 * C a) * dickson 2 a n ^ 2 =
      4 * C a ^ (n + 1) := by
  have h := dickson_second_cassini a n
  rw [dickson_add_two] at h
  rw [dickson_first_eq_second]
  linear_combination 4 * h

/-- Differentiation of the first kind gives the second kind in every characteristic. -/
theorem dickson_parameter_derivative (a : R) (n : ℕ) :
    (dickson 1 a (n + 1)).derivative =
      (n + 1 : R[X]) * dickson 2 a n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [dickson_zero, dickson_one]
  | one =>
    norm_num [dickson_zero, dickson_one, dickson_add_two, derivative_sub,
      derivative_mul, derivative_X, derivative_C]
    ring
  | more n h0 h1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, dickson_add_two,
      derivative_sub, derivative_mul, derivative_mul, derivative_X, derivative_C,
      one_mul, zero_mul, zero_add, h0, h1, dickson_first_eq_second,
      dickson_add_two]
    push_cast
    ring

/-- Differential energy for first-kind Dickson polynomials with arbitrary parameter. -/
theorem dickson_parameter_differential_energy (a : R) (n : ℕ) :
    (X ^ 2 - 4 * C a) * (dickson 1 a (n + 1)).derivative ^ 2 =
      (n + 1 : R[X]) ^ 2 * (dickson 1 a (n + 1) ^ 2 - 4 * C a ^ (n + 1)) := by
  rw [dickson_parameter_derivative]
  linear_combination -(n + 1 : R[X]) ^ 2 * dickson_parameter_pell a n

end GaloisForLFunctions.HTGeometry
