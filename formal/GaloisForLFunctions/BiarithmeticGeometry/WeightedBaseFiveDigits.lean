import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact weighted base-five rows

Evaluating the base-five digits at a real parameter gives the finite algebraic core of
prime-five geometric receivers. Digit splitting makes the dilation defect explicit before
any horizon or damping limit.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Evaluate the ordinary base-five digit polynomial at `a`. -/
def fiveDigitRow (a : ℝ) (n : ℕ) : ℝ := Nat.ofDigits a (Nat.digits 5 n)

theorem fiveDigitRow_zero (a : ℝ) : fiveDigitRow a 0 = 0 := by
  simp only [fiveDigitRow, Nat.digits_zero, Nat.ofDigits]

/-- One digit splits off with no approximation or carry term. -/
theorem fiveDigitRow_rec (a : ℝ) (n : ℕ) :
    fiveDigitRow a n = (n % 5 : ℕ) + a * fiveDigitRow a (n / 5) := by
  by_cases hn : n = 0
  · subst n
    rw [fiveDigitRow_zero]
    simp only [Nat.zero_mod, Nat.cast_zero, mul_zero, add_zero]
  · rw [fiveDigitRow, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn)]
    rfl

/-- Appending a least significant digit is an affine operation on the row. -/
theorem fiveDigitRow_affine (a : ℝ) (n r : ℕ) (hr : r < 5) :
    fiveDigitRow a (5 * n + r) = (r : ℝ) + a * fiveDigitRow a n := by
  rw [fiveDigitRow_rec]
  have hm : (5 * n + r) % 5 = r := by omega
  have hd : (5 * n + r) / 5 = n := by omega
  rw [hm, hd]

theorem fiveDigitRow_mul_five (a : ℝ) (n : ℕ) :
    fiveDigitRow a (5 * n) = a * fiveDigitRow a n := by
  simpa only [add_zero, Nat.cast_zero, zero_add] using fiveDigitRow_affine a n 0 (by omega)

/-- Concatenation of digit blocks gives an exact weighted dilation law. -/
theorem fiveDigitRow_concat (a : ℝ) (r n m : ℕ) (hm : m < 5 ^ r) :
    fiveDigitRow a (5 ^ r * n + m) = a ^ r * fiveDigitRow a n + fiveDigitRow a m := by
  induction r generalizing m with
  | zero =>
    have hm0 : m = 0 := by rw [pow_zero] at hm; omega
    subst m
    simp only [pow_zero, one_mul, add_zero, fiveDigitRow_zero]
  | succ r ih =>
    have hquot : m / 5 < 5 ^ r := by
      rw [pow_succ] at hm
      omega
    have hmod : m % 5 < 5 := Nat.mod_lt _ (by omega)
    have hsplit : 5 ^ (r + 1) * n + m = 5 * (5 ^ r * n + m / 5) + m % 5 := by
      have hdiv := Nat.mod_add_div m 5
      rw [pow_succ]
      nlinarith only [hdiv]
    rw [hsplit, fiveDigitRow_affine a _ _ hmod, ih _ hquot,
      fiveDigitRow_rec a m, pow_succ]
    ring

/-- Removing any number of base-five digits exposes the exact bounded remainder. -/
theorem fiveDigitRow_split (a : ℝ) (r n : ℕ) :
    a ^ r * fiveDigitRow a (n / 5 ^ r) =
      fiveDigitRow a n - fiveDigitRow a (n % 5 ^ r) := by
  have hp : 0 < 5 ^ r := pow_pos (by omega) r
  have h := fiveDigitRow_concat a r (n / 5 ^ r) (n % 5 ^ r) (Nat.mod_lt n hp)
  have hn : 5 ^ r * (n / 5 ^ r) + n % 5 ^ r = n := by
    have hdiv := Nat.mod_add_div n (5 ^ r)
    omega
  rw [hn] at h
  linarith only [h]

/-- Positive digit weights give a positive row. -/
theorem fiveDigitRow_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : 0 ≤ fiveDigitRow a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; rw [fiveDigitRow_zero]
    · rw [fiveDigitRow_rec]
      have hq : n / 5 < n := by omega
      exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg ha (ih _ hq))

/-- A one-digit row is independent of the evaluation parameter. -/
theorem fiveDigitRow_small (a : ℝ) (n : ℕ) (hn : n < 5) : fiveDigitRow a n = n := by
  rw [fiveDigitRow_rec, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, fiveDigitRow_zero,
    mul_zero, add_zero]

/-- The leading digit alone gives a sharp blockwise lower bound. -/
theorem fiveDigitRow_block_lower (a : ℝ) (ha : 0 ≤ a) (r n : ℕ)
    (hlo : 5 ^ r ≤ n) (hhi : n < 5 ^ (r + 1)) : a ^ r ≤ fiveDigitRow a n := by
  have hp : 0 < 5 ^ r := pow_pos (by omega) r
  have hquot0 : 1 ≤ n / 5 ^ r := Nat.one_le_div_iff hp |>.mpr hlo
  have hquot5 : n / 5 ^ r < 5 := by
    rw [pow_succ] at hhi
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [mul_comm] using hhi)
  have hsplit := fiveDigitRow_split a r n
  rw [fiveDigitRow_small a _ hquot5] at hsplit
  have hc : (1 : ℝ) ≤ (n / 5 ^ r : ℕ) := by exact_mod_cast hquot0
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg ha r)
  rw [mul_one] at hm
  have hrem := fiveDigitRow_nonneg a ha (n % 5 ^ r)
  linarith only [hsplit, hm, hrem]

/-- The exact one-step defect retains the least significant digit. -/
theorem fiveDigitRow_dilation_defect (a : ℝ) (n : ℕ) :
    fiveDigitRow a n - a * fiveDigitRow a (n / 5) = (n % 5 : ℕ) := by
  rw [fiveDigitRow_rec a n]
  ring

end GaloisForLFunctions.BiarithmeticGeometry
