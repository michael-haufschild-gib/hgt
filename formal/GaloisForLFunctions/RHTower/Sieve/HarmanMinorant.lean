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
  (primeWindow (n / q₁) z q₁).filter (fun q => q₁ * q ^ 4 < E)

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

/-- **The minorant is below the sifting function at level `Q`.**  Three Buchstab expansions and
two discarded nonnegative tails. -/
theorem rhoMinus_le_rho {z Q D E n : ℕ} (hn : 0 < n) (hzQ : z ≤ Q) (hDQ : D ≤ Q) :
    rhoMinus z Q D E n ≤ (rho n Q : ℤ) := by
  classical
  set W : Finset ℕ := primeWindow n z Q with hW
  -- the first Buchstab expansion
  have hB1 : rho n Q + ∑ q ∈ W, rho (n / q) q = rho n z := buchstab_window hn hzQ
  -- the second: every level-`q` term becomes a level-`z` term minus a double sum
  set Dsum : ℕ := ∑ q₁ ∈ W, ∑ q₂ ∈ primeWindow (n / q₁) z q₁, rho (n / q₁ / q₂) q₂ with hDsum
  have hB2 : harmanS1 z Q n = (∑ q ∈ W, rho (n / q) q) + Dsum := by
    rw [harmanS1, ← hW, hDsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hzq : z ≤ q := (mem_primeWindow.1 (hW ▸ hq)).1.1
    exact (buchstab_window (div_pos_of_mem_primeWindow hn (hW ▸ hq)) hzq).symm
  -- discarding the inadmissible pairs
  set DG : ℕ := ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁, rho (n / q₁ / q₂) q₂
    with hDG
  have hDGle : DG ≤ Dsum := by
    rw [hDG, hDsum]
    refine le_trans (Finset.sum_le_sum fun q₁ _ => ?_) ?_
    · exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    · exact Finset.sum_le_sum_of_subset (hW ▸ primeWindow_subset_right hDQ)
  -- the third Buchstab expansion, on the admissible pairs
  set Tsum : ℕ := ∑ q₁ ∈ primeWindow n z D, ∑ q₂ ∈ harmanPairs z E n q₁,
    ∑ q₃ ∈ primeWindow (n / q₁ / q₂) z q₂, rho (n / q₁ / q₂ / q₃) q₃ with hTsum
  have hB3 : harmanS2 z D E n = DG + Tsum := by
    rw [harmanS2, hDG, hTsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q₂ hq₂ => ?_
    have hq₂' : q₂ ∈ primeWindow (n / q₁) z q₁ := Finset.mem_of_mem_filter _ hq₂
    have hzq₂ : z ≤ q₂ := (mem_primeWindow.1 hq₂').1.1
    have hq₁0 : 0 < n / q₁ := div_pos_of_mem_primeWindow hn hq₁
    exact (buchstab_window (div_pos_of_mem_primeWindow hq₁0 hq₂') hzq₂).symm
  -- the third correction dominates the level-`q₃` sum
  have hT3 : Tsum ≤ harmanS3 z D E n := by
    rw [hTsum, harmanS3]
    refine Finset.sum_le_sum fun q₁ _ => Finset.sum_le_sum fun q₂ _ => ?_
    refine Finset.sum_le_sum fun q₃ hq₃ => ?_
    exact rho_antitone (mem_primeWindow.1 hq₃).1.1
  -- assemble
  have hB1Z : (rho n Q : ℤ) + (∑ q ∈ W, rho (n / q) q : ℕ) = (rho n z : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hB1
  have hB2Z : (harmanS1 z Q n : ℤ) = ((∑ q ∈ W, rho (n / q) q : ℕ) : ℤ) + (Dsum : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hB2
  have hB3Z : (harmanS2 z D E n : ℤ) = (DG : ℤ) + (Tsum : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) hB3
  have hDGZ : (DG : ℤ) ≤ (Dsum : ℤ) := by exact_mod_cast hDGle
  have hT3Z : (Tsum : ℤ) ≤ (harmanS3 z D E n : ℤ) := by exact_mod_cast hT3
  rw [rhoMinus]
  linarith [hB1Z, hB2Z, hB3Z, hDGZ, hT3Z]

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

end RHTower.Sieve
