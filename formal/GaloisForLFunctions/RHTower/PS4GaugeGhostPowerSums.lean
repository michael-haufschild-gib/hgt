import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# PS4 inversion of a quadratic Li gauge

The inverse Li/binomial transform of the quadratic gauge shift `c n²` has only
two nonzero coordinates: `c` in degree one and `-2c` in degree two.  The
higher vanishing is the standard fact that every forward difference of order
at least three annihilates a quadratic polynomial.
-/

open Finset Nat Function
open fwdDiff

namespace RHTower

/-- The PS4 inverse image of the quadratic gauge sequence, before multiplying by `c`. -/
def ps4QuadraticGhost (j : ℕ) : ℤ :=
  ∑ n ∈ range (j + 1), (-1 : ℤ) ^ (n + 1) * j.choose n * (n : ℤ) ^ 2

theorem neg_one_pow_ps4_sign {j n : ℕ} (hn : n ≤ j) :
    (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j - n) := by
  symm
  calc
    (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j - n) =
        (-1 : ℤ) ^ ((j + 1) + (j - n)) := by rw [← pow_add]
    _ = (-1 : ℤ) ^ (2 * (j - n) + (n + 1)) := by
      congr 1
      omega
    _ = ((-1 : ℤ) ^ 2) ^ (j - n) * (-1 : ℤ) ^ (n + 1) := by
      rw [pow_add, pow_mul]
    _ = (-1 : ℤ) ^ (n + 1) := by norm_num

theorem ps4QuadraticGhost_eq_signed_fwdDiff (j : ℕ) :
    ps4QuadraticGhost j =
      (-1 : ℤ) ^ (j + 1) *
        Δ_[(1 : ℤ)]^[j] (fun r : ℤ => r ^ 2) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [ps4QuadraticGhost, zero_add, nsmul_eq_mul, Int.reduceNeg, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnj : n ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  rw [neg_one_pow_ps4_sign hnj]
  ring

theorem ps4QuadraticGhost_one : ps4QuadraticGhost 1 = 1 := by
  norm_num [ps4QuadraticGhost, Finset.sum_range_succ]

theorem ps4QuadraticGhost_two : ps4QuadraticGhost 2 = -2 := by
  norm_num [ps4QuadraticGhost, Finset.sum_range_succ]

theorem ps4QuadraticGhost_eq_zero {j : ℕ} (hj : 3 ≤ j) :
    ps4QuadraticGhost j = 0 := by
  rw [ps4QuadraticGhost_eq_signed_fwdDiff]
  have hz : Δ_[(1 : ℤ)]^[j] (fun r : ℤ => r ^ 2) = 0 :=
    fwdDiff_iter_pow_eq_zero_of_lt (by omega)
  rw [hz]
  simp

/-- The real PS4 inverse image of the gauge shift `delta lambda_n = c n²`. -/
def ps4QuadraticGaugeGhost (c : ℝ) (j : ℕ) : ℝ :=
  c * (ps4QuadraticGhost j : ℝ)

/-- A quadratic Li-gauge shift produces exactly the two PS4 ghost power sums. -/
theorem ps4QuadraticGaugeGhost_classification (c : ℝ) :
    ps4QuadraticGaugeGhost c 1 = c ∧
      ps4QuadraticGaugeGhost c 2 = -2 * c ∧
      (∀ j, 3 ≤ j → ps4QuadraticGaugeGhost c j = 0) := by
  constructor
  · simp [ps4QuadraticGaugeGhost, ps4QuadraticGhost_one]
  constructor
  · simp [ps4QuadraticGaugeGhost, ps4QuadraticGhost_two]
    ring
  · intro j hj
    simp [ps4QuadraticGaugeGhost, ps4QuadraticGhost_eq_zero hj]

end RHTower
