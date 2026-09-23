import GaloisForLFunctions.RHTower.Sieve.RoughPairCount

/-!
# The shifted counts of the discarded set

The set the short-interval argument discards is the integers of `[1, N]` free of primes in
`(P₁, h]`.  Its shifted counts — the quantity the fibre second moment reduces to — are bounded by
the two-dimensional sieve, uniformly in the shift.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The integers of `[1, N]` free of primes in `(P₁, h]`. -/
def roughSet (P₁ h N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun m => ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)

/-- **A shifted count of the discarded set is bounded by the sieve.** -/
theorem card_shift_roughSet_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ))
    (D : Finset ℕ) :
    ((((roughSet P₁ h ⌊Y⌋₊ ∩ D).filter
        (fun m => m + d ∈ roughSet P₁ h ⌊Y⌋₊ ∩ D)).card : ℕ) : ℝ)
      ≤ Y / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
            * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        + ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  refine le_trans ?_ (card_roughPair_le Y hP₁ d k hz hY hh1 hP₁h hlev hk)
  have hsub : (roughSet P₁ h ⌊Y⌋₊ ∩ D).filter (fun m => m + d ∈ roughSet P₁ h ⌊Y⌋₊ ∩ D)
      ⊆ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
          ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_inter] at hm
    obtain ⟨⟨hmR, -⟩, hshift⟩ := hm
    rw [Finset.mem_inter] at hshift
    rw [roughSet, Finset.mem_filter] at hmR
    have hshiftR := hshift.1
    rw [roughSet, Finset.mem_filter] at hshiftR
    exact Finset.mem_filter.2 ⟨hmR.1, hmR.2, hshiftR.2⟩
  exact_mod_cast Finset.card_le_card hsub

end

end RHTower.Sieve
