import GaloisForLFunctions.RHTower.Sieve.RoughPairSieve

/-!
# The remainder of the two-dimensional sieve, bounded by the level

The Selberg remainder is a sum of `2·6^{ω(e)}` over the squarefree `e ≤ z` built from the sifting
primes.  Every such `e` has all its prime factors above `2`, so `3^{ω(e)} ≤ e` and hence
`6^{ω(e)} ≤ e²`; and the `e` are distinct positive integers below `z`.  The remainder is therefore
at most `2z³` — polynomial in the level, hence negligible against the main term whenever the level
is a small power of the range.
-/

namespace RHTower.Sieve

open Finset

/-- A squarefree divisor of the sifting primorial dominates `3` to its number of prime factors. -/
theorem three_pow_card_le {P₁ h e : ℕ} (hP₁ : 2 ≤ P₁) (he : e ∣ rangePrimorial P₁ h) :
    3 ^ e.primeFactors.card ≤ e := by
  classical
  have hsq : Squarefree e := (rangePrimorial_squarefree P₁ h).squarefree_of_dvd he
  have hprod : ∏ p ∈ e.primeFactors, p = e := Nat.prod_primeFactors_of_squarefree hsq
  have hthree : ∀ p ∈ e.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpe : p ∣ e := Nat.dvd_of_mem_primeFactors hp
    have hpP : p ∣ rangePrimorial P₁ h := hpe.trans he
    have hmem : p ∈ rangePrimes P₁ h :=
      mem_of_prime_dvd_prod (fun q hq => rangePrimes_prime hq) hpp hpP
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hmem
    omega
  calc 3 ^ e.primeFactors.card = ∏ _p ∈ e.primeFactors, 3 := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ e.primeFactors, p := Finset.prod_le_prod' hthree
    _ = e := hprod

/-- **The sieve remainder is at most `2z³`.** -/
theorem sieve_remainder_le {P₁ h : ℕ} (hP₁ : 2 ≤ P₁) {z : ℝ} (hz : 1 ≤ z) :
    ∑ e ∈ (rangePrimorial P₁ h).divisors,
        (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)
      ≤ 2 * z ^ (3 : ℕ) := by
  classical
  set T : Finset ℕ := (rangePrimorial P₁ h).divisors.filter (fun e => ((e : ℕ) : ℝ) ≤ z) with hT
  have hz0 : (0 : ℝ) < z := by linarith
  have hsum : ∑ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then (2 : ℝ) * 6 ^ e.primeFactors.card else 0)
      = ∑ e ∈ T, (2 : ℝ) * 6 ^ e.primeFactors.card := by
    rw [hT, Finset.sum_filter]
  rw [hsum]
  -- every term is at most `2z²`
  have hterm : ∀ e ∈ T, (2 : ℝ) * 6 ^ e.primeFactors.card ≤ 2 * z ^ (2 : ℕ) := by
    intro e he
    rw [hT, Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hdvd, hne⟩, hle⟩ := he
    have he0 : e ≠ 0 := by
      intro hc
      exact hne (by rw [hc] at hdvd; exact zero_dvd_iff.1 hdvd)
    have h3 := three_pow_card_le hP₁ hdvd
    have h3R : (3 : ℝ) ^ e.primeFactors.card ≤ (e : ℝ) := by exact_mod_cast h3
    have h6 : (6 : ℝ) ^ e.primeFactors.card ≤ (9 : ℝ) ^ e.primeFactors.card :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h9 : (9 : ℝ) ^ e.primeFactors.card = ((3 : ℝ) ^ e.primeFactors.card) ^ (2 : ℕ) := by
      rw [← pow_mul, show e.primeFactors.card * 2 = 2 * e.primeFactors.card by ring, pow_mul]
      norm_num
    have h30 : (0 : ℝ) ≤ (3 : ℝ) ^ e.primeFactors.card := by positivity
    have hsq : ((3 : ℝ) ^ e.primeFactors.card) ^ (2 : ℕ) ≤ (e : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ h30 h3R 2
    have hez : (e : ℝ) ^ (2 : ℕ) ≤ z ^ (2 : ℕ) := pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
    linarith [h6, h9, hsq, hez]
  -- there are at most `z` terms
  have hcard : ((T.card : ℕ) : ℝ) ≤ z := by
    have hsub : T ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro e he
      rw [hT, Finset.mem_filter, Nat.mem_divisors] at he
      obtain ⟨⟨hdvd, hne⟩, hle⟩ := he
      have he0 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | hpos
        · exact absurd (zero_dvd_iff.1 hdvd) hne
        · exact hpos
      rw [Finset.mem_Icc]
      exact ⟨he0, Nat.le_floor hle⟩
    have h1 : (T.card : ℕ) ≤ (Finset.Icc 1 ⌊z⌋₊).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((T.card : ℕ) : ℝ) ≤ ((⌊z⌋₊ + 1 - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((⌊z⌋₊ + 1 - 1 : ℕ) : ℝ) = ((⌊z⌋₊ : ℕ) : ℝ) := by
      congr 1
    rw [h3] at h2
    exact h2.trans (Nat.floor_le hz0.le)
  calc ∑ e ∈ T, (2 : ℝ) * 6 ^ e.primeFactors.card
      ≤ ∑ _e ∈ T, 2 * z ^ (2 : ℕ) := Finset.sum_le_sum hterm
    _ = ((T.card : ℕ) : ℝ) * (2 * z ^ (2 : ℕ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ z * (2 * z ^ (2 : ℕ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * z ^ (3 : ℕ) := by ring

end RHTower.Sieve
