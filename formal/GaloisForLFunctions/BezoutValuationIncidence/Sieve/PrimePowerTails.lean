import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# Reciprocal tails of proper prime powers

The fractional Mangoldt moment at exponent `9/16` gives a uniform
`H^(-7/16)` tail above every positive cutoff. No prime distribution
hypothesis enters the proper-power remainder.
-/

noncomputable section
open Finset
open RHTower
open ArithmeticFunction

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The proper-prime-power reciprocal mass above `H` has a uniform fractional-power tail. -/
theorem proper_prime_power_tail {H : ℝ} (hH : 0 < H) (X : ℕ) :
    ∑ n ∈ (Icc 1 X).filter (fun n : ℕ => ¬n.Prime ∧ H ≤ (n : ℝ)),
      vonMangoldt n / (n : ℝ) ≤ 576 * H ^ (-(7 / 16 : ℝ)) := by
  let S := (Icc 1 X).filter (fun n : ℕ => ¬n.Prime ∧ H ≤ (n : ℝ))
  have hsplit (n : ℕ) (hn : 0 < (n : ℝ)) :
      vonMangoldt n / (n : ℝ) =
        (vonMangoldt n * (n : ℝ) ^ (-(9 / 16 : ℝ))) * (n : ℝ) ^ (-(7 / 16 : ℝ)) := by
    rw [mul_assoc, ← Real.rpow_add hn,
      show -(9 / 16 : ℝ) + -(7 / 16 : ℝ) = -(1 : ℝ) by norm_num,
      Real.rpow_neg hn.le, Real.rpow_one]
    ring
  have hterm (n : ℕ) (hn : n ∈ S) :
      vonMangoldt n / (n : ℝ) ≤
        H ^ (-(7 / 16 : ℝ)) * (vonMangoldt n * (n : ℝ) ^ (-(9 / 16 : ℝ))) := by
    obtain ⟨_, _, hHn⟩ := mem_filter.mp hn
    have hn0 : 0 < (n : ℝ) := hH.trans_le hHn
    rw [hsplit n hn0, mul_comm (H ^ _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hH hHn (by norm_num))
      (mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hn0.le _))
  have hsub : S ⊆ (Icc 1 X).filter (fun n : ℕ => ¬n.Prime) := by
    intro n hn
    obtain ⟨hnX, hnp, _⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnX, hnp⟩
  have hm := sum_nonprime_vonMangoldt_rpow_le
    (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) ≤ 1) X
  norm_num only [show (1 / 2 : ℝ) + 1 / 16 = 9 / 16 by norm_num,
    show (36 : ℝ) / (1 / 16) = 576 by norm_num] at hm
  calc
    _ ≤ ∑ n ∈ S, H ^ (-(7 / 16 : ℝ)) *
        (vonMangoldt n * (n : ℝ) ^ (-(9 / 16 : ℝ))) := sum_le_sum hterm
    _ = H ^ (-(7 / 16 : ℝ)) * ∑ n ∈ S,
        vonMangoldt n * (n : ℝ) ^ (-(9 / 16 : ℝ)) := by rw [mul_sum]
    _ ≤ H ^ (-(7 / 16 : ℝ)) * 576 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hH.le _)
      refine (sum_le_sum_of_subset_of_nonneg hsub ?_).trans hm
      intro n _ _
      exact mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := by ring

#print axioms proper_prime_power_tail

end GaloisForLFunctions.BezoutValuationIncidence
