import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

/-!
# Cancellation of a power against an inverse power

Rewrite rules for `x ^ n * x⁻¹ ^ m` in a commutative group with zero, with the exponent
comparison as an explicit side condition so that `simp (disch := decide)` can apply them to
numeral exponents. They turn the Laurent-type normal forms produced by `ring_nf` (which cannot
cancel `x * x⁻¹` without a nonvanishing hypothesis) into forms in which each atom carries
either a positive or an inverse power, never both.
-/

namespace GaloisForLFunctions.HTGeometry.InversePowerCancellation

variable {G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0)
include hx

theorem pow_mul_inv_pow (n m : ℕ) (h : m ≤ n) : x ^ n * x⁻¹ ^ m = x ^ (n - m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, mul_right_comm, ← mul_pow, mul_inv_cancel₀ hx, one_pow,
    one_mul]

theorem pow_mul_inv_pow' (n m : ℕ) (h : n ≤ m) : x ^ n * x⁻¹ ^ m = x⁻¹ ^ (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow,
    one_mul]

theorem pow_mul_inv (n : ℕ) (h : 1 ≤ n) : x ^ n * x⁻¹ = x ^ (n - 1) := by
  simpa using pow_mul_inv_pow hx n 1 h

theorem mul_inv_pow (m : ℕ) (h : 1 ≤ m) : x * x⁻¹ ^ m = x⁻¹ ^ (m - 1) := by
  simpa using pow_mul_inv_pow' hx 1 m h

theorem mul_inv_self : x * x⁻¹ = 1 := mul_inv_cancel₀ hx

theorem mul_pow_mul_inv_pow (a : G) (n m : ℕ) (h : m ≤ n) :
    a * x ^ n * x⁻¹ ^ m = a * x ^ (n - m) := by
  rw [mul_assoc, pow_mul_inv_pow hx n m h]

theorem mul_pow_mul_inv_pow' (a : G) (n m : ℕ) (h : n ≤ m) :
    a * x ^ n * x⁻¹ ^ m = a * x⁻¹ ^ (m - n) := by
  rw [mul_assoc, pow_mul_inv_pow' hx n m h]

theorem mul_pow_mul_inv (a : G) (n : ℕ) (h : 1 ≤ n) : a * x ^ n * x⁻¹ = a * x ^ (n - 1) := by
  rw [mul_assoc, pow_mul_inv hx n h]

theorem mul_mul_inv_pow (a : G) (m : ℕ) (h : 1 ≤ m) : a * x * x⁻¹ ^ m = a * x⁻¹ ^ (m - 1) := by
  rw [mul_assoc, mul_inv_pow hx m h]

theorem mul_mul_inv_self (a : G) : a * x * x⁻¹ = a := by
  rw [mul_assoc, mul_inv_self hx, mul_one]

theorem inv_pow_mul_pow (n m : ℕ) (h : m ≤ n) : x⁻¹ ^ m * x ^ n = x ^ (n - m) := by
  rw [mul_comm, pow_mul_inv_pow hx n m h]

theorem inv_pow_mul_pow' (n m : ℕ) (h : n ≤ m) : x⁻¹ ^ m * x ^ n = x⁻¹ ^ (m - n) := by
  rw [mul_comm, pow_mul_inv_pow' hx n m h]

theorem inv_mul_pow (n : ℕ) (h : 1 ≤ n) : x⁻¹ * x ^ n = x ^ (n - 1) := by
  rw [mul_comm, pow_mul_inv hx n h]

theorem inv_pow_mul (m : ℕ) (h : 1 ≤ m) : x⁻¹ ^ m * x = x⁻¹ ^ (m - 1) := by
  rw [mul_comm, mul_inv_pow hx m h]

theorem inv_mul_self : x⁻¹ * x = 1 := inv_mul_cancel₀ hx

theorem mul_inv_pow_mul_pow (a : G) (n m : ℕ) (h : m ≤ n) :
    a * x⁻¹ ^ m * x ^ n = a * x ^ (n - m) := by
  rw [mul_assoc, inv_pow_mul_pow hx n m h]

theorem mul_inv_pow_mul_pow' (a : G) (n m : ℕ) (h : n ≤ m) :
    a * x⁻¹ ^ m * x ^ n = a * x⁻¹ ^ (m - n) := by
  rw [mul_assoc, inv_pow_mul_pow' hx n m h]

theorem mul_inv_mul_pow (a : G) (n : ℕ) (h : 1 ≤ n) : a * x⁻¹ * x ^ n = a * x ^ (n - 1) := by
  rw [mul_assoc, inv_mul_pow hx n h]

theorem mul_inv_pow_mul (a : G) (m : ℕ) (h : 1 ≤ m) : a * x⁻¹ ^ m * x = a * x⁻¹ ^ (m - 1) := by
  rw [mul_assoc, inv_pow_mul hx m h]

theorem mul_inv_mul_self (a : G) : a * x⁻¹ * x = a := by
  rw [mul_assoc, inv_mul_self hx, mul_one]

end GaloisForLFunctions.HTGeometry.InversePowerCancellation
