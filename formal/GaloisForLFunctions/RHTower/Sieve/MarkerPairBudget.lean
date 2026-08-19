import GaloisForLFunctions.RHTower.Sieve.MarkerLossDevice
import GaloisForLFunctions.RHTower.Sieve.PrimePairAverage
import GaloisForLFunctions.RHTower.Sieve.MarkerCountUpper

/-!
# The shifted-pair budget of a marker block

The device of `Sieve/MarkerLossDevice` consumes a bound on `∑_{d ≤ K} #{p ∈ M : p + d ∈ M}` for the
marker set `M`.  For a block of primes this is a sum of shifted prime-pair counts, which is exactly
what the two-dimensional Selberg sieve of `Sieve/PrimePairAverage` bounds: the pairs are `≪ K·Y`
divided by the square of the sifting saving, and that saving is two logarithms.
-/

namespace RHTower.Sieve

open Finset

/-- The shifted pairs of a marker block are shifted prime pairs above the sifting range. -/
theorem sum_card_shift_bigPrimeSet_le {M₀ b h : ℕ} (hhM : h ≤ M₀) (K : ℕ) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ b).filter (fun p => p + d ∈ bigPrimeSet M₀ b)).card : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 K,
          ((((Finset.Icc 1 b).filter
              (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ) := by
  classical
  refine Finset.sum_le_sum fun d _ => ?_
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpM, hpd⟩ := hp
  have hprime := prime_of_mem_bigPrimeSet hpM
  have hdprime := prime_of_mem_bigPrimeSet hpd
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hpM
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, hpM.1.2⟩, hprime, hdprime, by omega⟩

/-- **The shifted-pair budget of a marker block, from the two-dimensional sieve.** -/
theorem sum_card_shift_bigPrimeSet_le_sieve {M₀ b : ℕ} {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    (K k : ℕ) {z : ℝ} (hz : 1 ≤ z) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hhM : h ≤ M₀)
    (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2 ≤ (k : ℝ)) :
    ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet M₀ b).filter (fun p => p + d ∈ bigPrimeSet M₀ b)).card : ℕ) : ℝ)
      ≤ 2 * Real.exp 1 * (K : ℝ) * (b : ℝ) / (Real.exp (mertensS h - mertensS P₁)) ^ 2
        + (K : ℝ) * ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  have hfloor : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hsieve := sum_card_primePair_le ((b : ℕ) : ℝ) hP₁ K k hz (Nat.cast_nonneg b) hh1 hP₁h
    hlev hk
  rw [hfloor] at hsieve
  exact le_trans (sum_card_shift_bigPrimeSet_le hhM K) hsieve

end RHTower.Sieve
