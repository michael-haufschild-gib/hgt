import GaloisForLFunctions.BiarithmeticGeometry.WeightedDigitEnumeration
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# Pronic energy on complete digit blocks

The exact digit variance survives comparison with the largest denominator in a block.
The reciprocal telescope and the digit bound give the complementary upper estimate.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Pronic energy of an arbitrary signed digit row on one complete base-five block. -/
def fiveDigitPronicBlock (x : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)),
    fiveWeightedDigitRow x n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- The complete block has its exact telescoping pronic mass. -/
theorem fiveBlock_pronic_mass (M : ℕ) :
    (∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)), 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      4 / (5 * (5 : ℝ) ^ M) := by
  have hle : 5 ^ M ≤ 5 ^ (M + 1) := by rw [pow_succ]; omega
  have ht := sum_Ico_sub (f := fun n : ℕ => -(1 / (n : ℝ))) hle
  have hterm (n : ℕ) (hn : n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1))) :
      -(1 / ((n + 1 : ℕ) : ℝ)) - -(1 / (n : ℝ)) =
        1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hp : 0 < 5 ^ M := pow_pos (by omega) M
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hp (mem_Ico.mp hn).1).ne'
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hn0, hn1]
    ring
  rw [sum_congr rfl hterm] at ht
  rw [ht]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_succ]
  have hp : (5 : ℝ) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hp]
  ring

/-- The leading digit variance gives a lower energy bound independently of all other signs. -/
theorem fiveDigitPronicBlock_lower (x : ℕ → ℝ) (M : ℕ) :
    x M ^ 2 / (5 : ℝ) ^ (M + 1) ≤ fiveDigitPronicBlock x M := by
  have hq : 0 < (5 : ℝ) ^ (M + 1) := by positivity
  calc
    _ = ((5 : ℝ) ^ (M + 1) * x M ^ 2) / ((5 : ℝ) ^ (M + 1)) ^ 2 := by
      field_simp [hq.ne']
    _ ≤ (∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)), fiveWeightedDigitRow x n ^ 2) /
        ((5 : ℝ) ^ (M + 1)) ^ 2 :=
      div_le_div_of_nonneg_right (fiveWeightedDigitRow_block_lower x M) (sq_nonneg _)
    _ ≤ _ := by
      rw [div_eq_mul_inv, sum_mul, fiveDigitPronicBlock]
      apply sum_le_sum
      intro n hn
      have hnat : 0 < n := lt_of_lt_of_le (pow_pos (by omega : 0 < 5) M) (mem_Ico.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hnat
      have hn1 : (n : ℝ) + 1 ≤ (5 : ℝ) ^ (M + 1) := by
        exact_mod_cast (Nat.add_one_le_iff.mpr (mem_Ico.mp hn).2)
      have hnle : (n : ℝ) ≤ (5 : ℝ) ^ (M + 1) := by linarith only [hn1]
      have hden : (n : ℝ) * ((n : ℝ) + 1) ≤ ((5 : ℝ) ^ (M + 1)) ^ 2 := by
        simpa only [pow_two] using mul_le_mul hnle hn1 (by positivity) hq.le
      exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hn0 (by positivity)) hden

private theorem abs_fiveWeightedDigitRow_on_block (x : ℕ → ℝ) (M n : ℕ)
    (hlo : 5 ^ M ≤ n) (hhi : n < 5 ^ (M + 1)) :
    |fiveWeightedDigitRow x n| ≤ 4 * ∑ i : Fin (M + 1), |x i| := by
  rw [fiveWeightedDigitRow_on_block x M n hlo hhi, fiveTruncatedDigitReadout, mul_sum]
  calc
    _ ≤ ∑ i : Fin (M + 1), |((n / 5 ^ (i : ℕ) % 5 : ℕ) : ℝ) * x i| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, Nat.abs_cast]
      have hd : n / 5 ^ (i : ℕ) % 5 ≤ 4 := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (abs_nonneg _)

/-- A block upper bound depends only on the absolute digit-weight sum. -/
theorem fiveDigitPronicBlock_upper (x : ℕ → ℝ) (M : ℕ) :
    fiveDigitPronicBlock x M ≤
      (64 / 5 : ℝ) * (∑ i : Fin (M + 1), |x i|) ^ 2 / (5 : ℝ) ^ M := by
  have hpoint (n : ℕ) (hn : n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1))) :
      fiveWeightedDigitRow x n ^ 2 ≤ (4 * ∑ i : Fin (M + 1), |x i|) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (fiveWeightedDigitRow x n))
      (abs_fiveWeightedDigitRow_on_block x M n (mem_Ico.mp hn).1 (mem_Ico.mp hn).2) 2
  calc
    _ ≤ (4 * ∑ i : Fin (M + 1), |x i|) ^ 2 *
        ∑ n ∈ Ico ((5 : ℕ) ^ M) (5 ^ (M + 1)), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [fiveDigitPronicBlock, mul_sum]
      apply sum_le_sum
      intro n hn
      simpa only [mul_one_div] using div_le_div_of_nonneg_right (hpoint n hn)
        (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))
    _ = _ := by rw [fiveBlock_pronic_mass]; ring

end GaloisForLFunctions.BiarithmeticGeometry
