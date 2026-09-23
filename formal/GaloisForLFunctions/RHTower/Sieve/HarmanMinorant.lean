import GaloisForLFunctions.RHTower.Sieve.BuchstabIdentity

/-!
# Harman's minorant for the primes

Applying Buchstab's identity three times to `rho n Q` and discarding the two nonnegative tails
gives a function below the indicator of the primes:

```text
   rhoMinus z Q D E n = rho n z − S₁ + S₂ − S₃
```

with `S₁` the sum over one prime divisor in `[z, Q)`, `S₂` the sum over admissible pairs
`z ≤ q₂ < q₁ < D` with `q₁q₂⁴ < E`, and `S₃` the sum over admissible triples.  This is the minorant
of Matomäki–Teräväinen, *Almost primes in almost all short intervals II*, (2.3), at the parameters
`z`, `Q = 2X^{1/2}`, `D = X^{1/4−2ε}`, `E = X^{1−2ε}`.
-/

namespace RHTower.Sieve

open Finset

/-- The prime divisors of `n` in the window `[a, b)`. -/
def primeWindow (n a b : ℕ) : Finset ℕ := (Finset.Ico a b).filter (fun q => q.Prime ∧ q ∣ n)

theorem mem_primeWindow {n a b q : ℕ} :
    q ∈ primeWindow n a b ↔ (a ≤ q ∧ q < b) ∧ q.Prime ∧ q ∣ n := by
  rw [primeWindow, Finset.mem_filter, Finset.mem_Ico]

theorem primeWindow_subset_right {n a b c : ℕ} (hbc : b ≤ c) :
    primeWindow n a b ⊆ primeWindow n a c := by
  intro q hq
  rw [mem_primeWindow] at hq ⊢
  exact ⟨⟨hq.1.1, by omega⟩, hq.2⟩

theorem div_pos_of_mem_primeWindow {n a b q : ℕ} (hn : 0 < n) (hq : q ∈ primeWindow n a b) :
    0 < n / q := by
  rw [mem_primeWindow] at hq
  exact Nat.div_pos (Nat.le_of_dvd hn hq.2.2) hq.2.1.pos

/-- Buchstab's identity with the window written as a prime window. -/
theorem buchstab_window {n w z : ℕ} (hn : 0 < n) (hwz : w ≤ z) :
    rho n z + ∑ q ∈ primeWindow n w z, rho (n / q) q = rho n w := buchstab hn hwz

/-- Harman's admissible second prime: `q₂ < q₁` with `q₁q₂⁴ < E`. -/
def harmanPairs (z E n q₁ : ℕ) : Finset ℕ :=
  (primeWindow (n / q₁) z q₁).filter (fun q => q₁ * q ^ (4 : ℕ) < E)

/-- The one-prime correction. -/
def harmanS1 (z Q n : ℕ) : ℕ := ∑ q ∈ primeWindow n z Q, rho (n / q) z

/-- The two-prime correction, over admissible pairs. -/
def harmanS2 (z D E n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁, rho (n / q₁ / q₂) z

/-- The three-prime correction, over admissible pairs extended by a third prime. -/
def harmanS3 (z D E n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁,
    ∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂, rho (n / q₁ / q₂ / q₃) z

/-- **Harman's minorant.** -/
def rhoMinus (z Q D E n : ℕ) : ℤ :=
  (rho n z : ℤ) - (harmanS1 z Q n : ℤ) + (harmanS2 z D E n : ℤ) - (harmanS3 z D E n : ℤ)

/-- The one-prime Buchstab remainder, still at level `q`. -/
def harmanR1 (z Q n : ℕ) : ℕ := ∑ q ∈ primeWindow n z Q, rho (n / q) q

/-- The full two-prime Buchstab remainder, at level `q₂`. -/
def harmanR2 (z Q n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z Q, ∑ q₂ ∈ primeWindow (n / q₁) z q₁, rho (n / q₁ / q₂) q₂

/-- The admissible two-prime remainder, at level `q₂`. -/
def harmanR2adm (z D E n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁, rho (n / q₁ / q₂) q₂

/-- The admissible three-prime remainder, at level `q₃`. -/
def harmanR3 (z D E n : ℕ) : ℕ :=
  ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁,
    ∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂, rho (n / q₁ / q₂ / q₃) q₃

/-- The first Buchstab expansion. -/
theorem harman_step_one {z Q n : ℕ} (hn : 0 < n) (hzQ : z ≤ Q) :
    rho n Q + harmanR1 z Q n = rho n z := buchstab_window hn hzQ

/-- The second Buchstab expansion, applied inside the one-prime remainder. -/
theorem harman_step_two {z Q n : ℕ} (hn : 0 < n) :
    harmanS1 z Q n = harmanR1 z Q n + harmanR2 z Q n := by
  rw [harmanS1, harmanR1, harmanR2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  exact (buchstab_window (div_pos_of_mem_primeWindow hn hq) (mem_primeWindow.1 hq).1.1).symm

/-- Discarding the inadmissible pairs. -/
theorem harmanR2adm_le {z Q D E n : ℕ} (hDQ : D ≤ Q) :
    harmanR2adm z D E n ≤ harmanR2 z Q n := by
  rw [harmanR2adm, harmanR2]
  have step1 : (∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁, rho (n / q₁ / q₂) q₂)
      ≤ ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ primeWindow (n / q₁) z q₁, rho (n / q₁ / q₂) q₂ :=
    Finset.sum_le_sum fun q₁ _ => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have step2 : (∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ primeWindow (n / q₁) z q₁, rho (n / q₁ / q₂) q₂)
      ≤ ∑ q₁ ∈ primeWindow n z Q, ∑ q₂ ∈ primeWindow (n / q₁) z q₁, rho (n / q₁ / q₂) q₂ :=
    Finset.sum_le_sum_of_subset (primeWindow_subset_right hDQ)
  exact le_trans step1 step2

/-- The third Buchstab expansion, applied inside the admissible two-prime remainder. -/
theorem harman_step_three {z D E n : ℕ} (hn : 0 < n) :
    harmanS2 z D E n = harmanR2adm z D E n + harmanR3 z D E n := by
  rw [harmanS2, harmanR2adm, harmanR3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q₂ hq₂ => ?_
  have hq₂' : q₂ ∈ primeWindow (n / q₁) z q₁ := Finset.mem_of_mem_filter _ hq₂
  have hq₁0 : 0 < n / q₁ := div_pos_of_mem_primeWindow hn hq₁
  exact (buchstab_window (div_pos_of_mem_primeWindow hq₁0 hq₂') (mem_primeWindow.1 hq₂').1.1).symm

/-- Raising the level of the innermost sum. -/
theorem harmanR3_le {z D E n : ℕ} : harmanR3 z D E n ≤ harmanS3 z D E n := by
  rw [harmanR3, harmanS3]
  exact Finset.sum_le_sum fun q₁ _ => Finset.sum_le_sum fun q₂ _ =>
    Finset.sum_le_sum fun q₃ hq₃ => rho_antitone (mem_primeWindow.1 hq₃).1.1

/-- **The minorant is below the sifting function at level `Q`.**  Three Buchstab expansions and
two discarded nonnegative tails. -/
theorem rhoMinus_le_rho {z Q D E n : ℕ} (hn : 0 < n) (hzQ : z ≤ Q) (hDQ : D ≤ Q) :
    rhoMinus z Q D E n ≤ (rho n Q : ℤ) := by
  have h1 : (rho n Q : ℤ) + (harmanR1 z Q n : ℤ) = (rho n z : ℤ) := by
    exact_mod_cast harman_step_one hn hzQ
  have h2 : (harmanS1 z Q n : ℤ) = (harmanR1 z Q n : ℤ) + (harmanR2 z Q n : ℤ) := by
    exact_mod_cast harman_step_two (z := z) (Q := Q) hn
  have h3 : (harmanS2 z D E n : ℤ) = (harmanR2adm z D E n : ℤ) + (harmanR3 z D E n : ℤ) := by
    exact_mod_cast harman_step_three (z := z) (D := D) (E := E) hn
  have h4 : (harmanR2adm z D E n : ℤ) ≤ (harmanR2 z Q n : ℤ) := by
    exact_mod_cast harmanR2adm_le (z := z) (E := E) (n := n) hDQ
  have h5 : (harmanR3 z D E n : ℤ) ≤ (harmanS3 z D E n : ℤ) := by
    exact_mod_cast harmanR3_le (z := z) (D := D) (E := E) (n := n)
  rw [rhoMinus]
  linarith

/-- **The sifting function at level `Q` detects the primes in `[Q, Q²)`.** -/
theorem rho_eq_prime_indicator {Q n : ℕ} (hQ : 2 ≤ Q) (hQn : Q ≤ n) (hnQ : n < Q * Q) :
    rho n Q = if n.Prime then 1 else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp]
    refine rho_eq_one_of (by omega) fun r hr => ?_
    have hrn : r = n := by
      have := Nat.mem_primeFactors.1 hr
      exact ((Nat.prime_dvd_prime_iff_eq this.1 hp).1 this.2.1)
    omega
  · rw [if_neg hp]
    rw [rho_eq_zero_iff]
    rintro ⟨-, hall⟩
    -- `n` has a prime factor, and every prime factor is at least `Q`
    have hn1 : 1 < n := by omega
    obtain ⟨r, hrp, hrn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hrmem : r ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hrp, hrn, by omega⟩
    have hrQ : Q ≤ r := hall r hrmem
    obtain ⟨m, hm⟩ := hrn
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge 1 m with h | h
      · exact h
      · interval_cases m
        · omega
        · exact absurd (by omega : n = r) (by rintro rfl; exact hp hrp)
    obtain ⟨s, hsp, hsm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hsn : s ∣ n := hm ▸ hsm.mul_left r
    have hsmem : s ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hsp, hsn, by omega⟩
    have hsQ : Q ≤ s := hall s hsmem
    have hsle : s ≤ m := Nat.le_of_dvd (by omega) hsm
    have : Q * Q ≤ r * m := Nat.mul_le_mul hrQ (le_trans hsQ hsle)
    omega

/-- **Harman's function is a minorant for the primes.** -/
theorem rhoMinus_le_primeIndicator {z Q D E n : ℕ} (hn : 0 < n) (hQ : 2 ≤ Q) (hzQ : z ≤ Q)
    (hDQ : D ≤ Q) (hQn : Q ≤ n) (hnQ : n < Q * Q) :
    rhoMinus z Q D E n ≤ (if n.Prime then 1 else 0 : ℤ) := by
  have h := rhoMinus_le_rho (z := z) (Q := Q) (D := D) (E := E) hn hzQ hDQ
  rw [rho_eq_prime_indicator hQ hQn hnQ] at h
  refine h.trans (le_of_eq ?_)
  by_cases hp : n.Prime <;> simp [hp]

/-! ## The size of the minorant -/

/-- The number of distinct prime factors of `n` that are at least `z`. -/
def largePrimeCount (n z : ℕ) : ℕ := (n.primeFactors.filter (fun p => z ≤ p)).card

theorem largePrimeCount_mono_dvd {m n z : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    largePrimeCount m z ≤ largePrimeCount n z := by
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact Nat.primeFactors_mono hmn hn

theorem card_primeWindow_le' {n z Q : ℕ} (hn : 0 < n) :
    (primeWindow n z Q).card ≤ largePrimeCount n z := by
  classical
  refine Finset.card_le_card ?_
  intro q hq
  rw [mem_primeWindow] at hq
  rw [Finset.mem_filter]
  exact ⟨Nat.mem_primeFactors.2 ⟨hq.2.1, hq.2.2, by omega⟩, hq.1.1⟩

theorem harmanS1_le {z Q n : ℕ} (hn : 0 < n) : harmanS1 z Q n ≤ largePrimeCount n z := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun q _ => rho_le_one _ _) ?_
  simpa using card_primeWindow_le' (z := z) (Q := Q) hn

theorem harmanS2_le {z D E n : ℕ} (hn : 0 < n) :
    harmanS2 z D E n ≤ largePrimeCount n z * largePrimeCount n z := by
  classical
  have hinner : ∀ q₁ ∈ primeWindow n z D,
      (∑ q₂ ∈ harmanPairs z E n q₁, rho (n / q₁ / q₂) z) ≤ largePrimeCount n z := by
    intro q₁ hq₁
    have hq₁0 : 0 < n / q₁ := div_pos_of_mem_primeWindow hn hq₁
    have hdvd : n / q₁ ∣ n := Nat.div_dvd_of_dvd (mem_primeWindow.1 hq₁).2.2
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun q₂ _ => rho_le_one _ _) ?_
    have hcard : (harmanPairs z E n q₁).card ≤ largePrimeCount n z := by
      refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
      exact le_trans (card_primeWindow_le' hq₁0) (largePrimeCount_mono_dvd hdvd (by omega))
    simpa using hcard
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_primeWindow_le' hn)

theorem harmanS3_le {z D E n : ℕ} (hn : 0 < n) :
    harmanS3 z D E n ≤ largePrimeCount n z * largePrimeCount n z * largePrimeCount n z := by
  classical
  have hinner : ∀ q₁ ∈ primeWindow n z D,
      (∑ q₂ ∈ harmanPairs z E n q₁,
        ∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂, rho (n / q₁ / q₂ / q₃) z)
      ≤ largePrimeCount n z * largePrimeCount n z := by
    intro q₁ hq₁
    have hq₁0 : 0 < n / q₁ := div_pos_of_mem_primeWindow hn hq₁
    have hdvd1 : n / q₁ ∣ n := Nat.div_dvd_of_dvd (mem_primeWindow.1 hq₁).2.2
    have hmid : ∀ q₂ ∈ harmanPairs z E n q₁,
        (∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂, rho (n / q₁ / q₂ / q₃) z)
        ≤ largePrimeCount n z := by
      intro q₂ hq₂
      have hq₂' : q₂ ∈ primeWindow (n / q₁) z q₁ := Finset.mem_of_mem_filter _ hq₂
      have hq₂0 : 0 < n / q₁ / q₂ := div_pos_of_mem_primeWindow hq₁0 hq₂'
      have hdvd2 : n / q₁ / q₂ ∣ n :=
        (Nat.div_dvd_of_dvd (mem_primeWindow.1 hq₂').2.2).trans hdvd1
      refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun q₃ _ => rho_le_one _ _) ?_
      have hcard : (primeWindow (n / q₁ / q₂) z q₂).card ≤ largePrimeCount n z :=
        le_trans (card_primeWindow_le' hq₂0) (largePrimeCount_mono_dvd hdvd2 (by omega))
      simpa using hcard
    refine le_trans (Finset.sum_le_sum hmid) ?_
    rw [Finset.sum_const, smul_eq_mul]
    refine Nat.mul_le_mul_right _ ?_
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    exact le_trans (card_primeWindow_le' hq₁0) (largePrimeCount_mono_dvd hdvd1 (by omega))
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [Finset.sum_const, smul_eq_mul]
  have := card_primeWindow_le' (z := z) (Q := D) hn
  calc (primeWindow n z D).card * (largePrimeCount n z * largePrimeCount n z)
      ≤ largePrimeCount n z * (largePrimeCount n z * largePrimeCount n z) :=
        Nat.mul_le_mul_right _ this
    _ = largePrimeCount n z * largePrimeCount n z * largePrimeCount n z := by ring

/-- **The minorant is bounded by a cube of the large-prime count.**  This is the elementary
majorant `(2.4)`: since `n` has at most `log n / log z` prime factors above `z`, the four terms of
`rhoMinus` have at most `1`, `K`, `K²`, `K³` nonzero summands. -/
theorem abs_rhoMinus_le {z Q D E n : ℕ} (hn : 0 < n) :
    |rhoMinus z Q D E n|
      ≤ 1 + (largePrimeCount n z : ℤ) + (largePrimeCount n z : ℤ) ^ (2 : ℕ)
        + (largePrimeCount n z : ℤ) ^ (3 : ℕ) := by
  have h0 : (rho n z : ℤ) ≤ 1 := by exact_mod_cast rho_le_one n z
  have h0' : (0 : ℤ) ≤ (rho n z : ℤ) := Int.natCast_nonneg _
  have h1 : (harmanS1 z Q n : ℤ) ≤ (largePrimeCount n z : ℤ) := by
    exact_mod_cast harmanS1_le (z := z) (Q := Q) hn
  have h1' : (0 : ℤ) ≤ (harmanS1 z Q n : ℤ) := Int.natCast_nonneg _
  have h2 : (harmanS2 z D E n : ℤ) ≤ (largePrimeCount n z : ℤ) ^ (2 : ℕ) := by
    have := harmanS2_le (z := z) (D := D) (E := E) hn
    have hc : ((harmanS2 z D E n : ℕ) : ℤ)
        ≤ ((largePrimeCount n z * largePrimeCount n z : ℕ) : ℤ) := by exact_mod_cast this
    calc (harmanS2 z D E n : ℤ) ≤ ((largePrimeCount n z * largePrimeCount n z : ℕ) : ℤ) := hc
      _ = (largePrimeCount n z : ℤ) ^ (2 : ℕ) := by push_cast; ring
  have h2' : (0 : ℤ) ≤ (harmanS2 z D E n : ℤ) := Int.natCast_nonneg _
  have h3 : (harmanS3 z D E n : ℤ) ≤ (largePrimeCount n z : ℤ) ^ (3 : ℕ) := by
    have := harmanS3_le (z := z) (D := D) (E := E) hn
    have hc : ((harmanS3 z D E n : ℕ) : ℤ)
        ≤ ((largePrimeCount n z * largePrimeCount n z * largePrimeCount n z : ℕ) : ℤ) := by
      exact_mod_cast this
    calc (harmanS3 z D E n : ℤ)
        ≤ ((largePrimeCount n z * largePrimeCount n z * largePrimeCount n z : ℕ) : ℤ) := hc
      _ = (largePrimeCount n z : ℤ) ^ (3 : ℕ) := by push_cast; ring
  have h3' : (0 : ℤ) ≤ (harmanS3 z D E n : ℤ) := Int.natCast_nonneg _
  rw [abs_le, rhoMinus]
  constructor <;> linarith

/-! ## The large-prime count against the logarithm -/

/-- **`z^K ≤ n`**: the distinct prime factors above `z` multiply into a divisor of `n`. -/
theorem pow_largePrimeCount_le {n z : ℕ} (hn : 0 < n) :
    z ^ largePrimeCount n z ≤ n := by
  classical
  set S : Finset ℕ := n.primeFactors.filter (fun p => z ≤ p) with hS
  have hdvd : (∏ p ∈ S, p) ∣ n := by
    refine dvd_trans (Finset.prod_dvd_prod_of_subset S n.primeFactors id ?_) ?_
    · rw [hS]; exact Finset.filter_subset _ _
    · exact Nat.prod_primeFactors_dvd n
  have hle : z ^ S.card ≤ ∏ p ∈ S, p := by
    calc z ^ S.card = ∏ _p ∈ S, z := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' fun p hp => (Finset.mem_filter.1 hp).2
  exact le_trans hle (Nat.le_of_dvd hn hdvd)

end RHTower.Sieve
