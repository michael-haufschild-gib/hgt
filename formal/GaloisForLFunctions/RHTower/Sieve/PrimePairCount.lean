import GaloisForLFunctions.RHTower.Sieve.RoughPairCount

/-!
# Prime pairs at a fixed shift

A prime above the sifting range carries no prime factor inside the range, so the shifted rough-pair
sieve of `Sieve/RoughPairCount` bounds the number of `m ≤ Y` for which both `m` and `m + d` are
prime and `m` exceeds the range.  This is the classical two-dimensional upper-bound sieve for prime
pairs, with the singular series appearing as the explicit shift correction

```text
C(d) = ∏_{p ∣ d, P₁ < p ≤ h} (p − 1)/p .
```

Nothing here is asymptotic: the bound is an inequality between explicit quantities, uniform in the
shift `d`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A prime above the sifting range is not divisible by any prime of the range. -/
theorem not_dvd_of_prime_lt {P₁ h m p : ℕ} (hm : m.Prime) (hmh : h < m)
    (hp : p ∈ rangePrimes P₁ h) : ¬ p ∣ m := by
  intro hdvd
  have hpp : p.Prime := rangePrimes_prime hp
  have heq : p = m := (Nat.prime_dvd_prime_iff_eq hpp hm).1 hdvd
  rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
  omega

/-- The prime pairs above the range sit inside the rough pairs. -/
theorem primePair_subset_roughPair (Y : ℝ) (P₁ h d : ℕ) :
    ((Finset.Icc 1 ⌊Y⌋₊).filter (fun m => m.Prime ∧ (m + d).Prime ∧ h < m))
      ⊆ (Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
            ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d)) := by
  classical
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  refine ⟨hm.1, fun p hp => not_dvd_of_prime_lt hm.2.1 hm.2.2.2 hp, fun p hp => ?_⟩
  exact not_dvd_of_prime_lt hm.2.2.1 (by omega) hp

/-- **The two-dimensional sieve for prime pairs.**  The number of primes `m ≤ Y` above the sifting
range with `m + d` also prime is at most the rough-pair bound. -/
theorem card_primePair_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ)) :
    ((((Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => m.Prime ∧ (m + d).Prime ∧ h < m)).card : ℕ) : ℝ)
      ≤ Y / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ)
            * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        + ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  refine le_trans ?_ (card_roughPair_le Y hP₁ d k hz hY hh1 hP₁h hlev hk)
  exact_mod_cast Nat.cast_le.2 (Finset.card_le_card (primePair_subset_roughPair Y P₁ h d))

end

end RHTower.Sieve
