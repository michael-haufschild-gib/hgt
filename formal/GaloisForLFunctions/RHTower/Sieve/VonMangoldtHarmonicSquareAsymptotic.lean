import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorEnergyExpansion
import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqLower

/-!
# Harmonic square asymptotic for the von Mangoldt weight

The prime part supplies the lower bound, while `Lambda(k)^2 <= Lambda(k) log k` and the existing
explicit harmonic `Lambda log` estimate supply the upper bound.  The result retains an explicit
`O(log N)` remainder around the sharp `one-half log-squared N` main term.
-/

noncomputable section

open Finset ArithmeticFunction

namespace RHTower.Sieve

theorem vonMangoldtHarmonicSquareSum_eq_Icc_one
    (N : ℕ) (hN : 1 ≤ N) :
    vonMangoldtHarmonicSquareSum N =
      ∑ k ∈ Finset.Icc 1 N, (Λ k) ^ 2 / (k : ℝ) := by
  rw [vonMangoldtHarmonicSquareSum]
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp), show Λ 1 = 0 by simp]
  norm_num

/-- The prime part is a lower bound for the full von Mangoldt harmonic square moment. -/
theorem sum_prime_log_sq_div_le_vonMangoldtHarmonicSquareSum
    (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) ^ 2 / (p : ℝ) ≤
      vonMangoldtHarmonicSquareSum N := by
  rw [vonMangoldtHarmonicSquareSum_eq_Icc_one N hN]
  rw [← filter_prime_Icc_eq_primesLE N]
  have hprime :
      ∑ p ∈ {m ∈ Finset.Icc 1 N | m.Prime},
          Real.log (p : ℝ) ^ 2 / (p : ℝ) =
        ∑ p ∈ {m ∈ Finset.Icc 1 N | m.Prime},
          (Λ p) ^ 2 / (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [hprime]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun m => m.Prime) (Finset.Icc 1 N))
    (fun k hk hnot => by positivity)

/-- The full harmonic square moment is bounded above by the `Lambda log/id` summatory. -/
theorem vonMangoldtHarmonicSquareSum_le_sum_vonMangoldt_log_div
    (N : ℕ) (hN : 1 ≤ N) :
    vonMangoldtHarmonicSquareSum N ≤
      ∑ k ∈ Finset.Icc 1 N, Λ k * Real.log k / (k : ℝ) := by
  rw [vonMangoldtHarmonicSquareSum_eq_Icc_one N hN]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
  have hΛ0 : 0 ≤ Λ k := vonMangoldt_nonneg
  have hΛlog : Λ k ≤ Real.log k := vonMangoldt_le_log
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hsq : (Λ k) ^ 2 ≤ Λ k * Real.log k := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hΛlog hΛ0
  exact div_le_div_of_nonneg_right hsq hkR.le

/-- Explicit asymptotic remainder for the von Mangoldt harmonic square moment. -/
theorem abs_vonMangoldtHarmonicSquareSum_sub_le
    (N : ℕ) (hN : 1 ≤ N) :
    |vonMangoldtHarmonicSquareSum N - Real.log N ^ 2 / 2| ≤
      39 * Real.log N + 25 := by
  rw [abs_le]
  constructor
  · have hprime := sum_prime_log_sq_div_ge N hN
    have hsub := sum_prime_log_sq_div_le_vonMangoldtHarmonicSquareSum N hN
    linarith
  · have hupper := vonMangoldtHarmonicSquareSum_le_sum_vonMangoldt_log_div N hN
    have hmain := RHTower.abs_sum_vonMangoldt_log_div_sub_le N hN
    rw [abs_le] at hmain
    have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    linarith

end RHTower.Sieve
