import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicMaskedRamare

/-!
# Active final primes after the initial non-rough projection

An integer in the final shell which carries an initial-range prime cannot also carry a final
prime above the shell top divided by the initial lower endpoint.  This file retains that exact
support restriction.  It is the factor which makes the initial exceptional-set volume affordable
in the second Ramaré receiver.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Final designated primes which can coexist below `B` with a prime strictly above `Q₀`. -/
def maskedActivePrimes (Q₀ : ℝ) (P : Finset ℕ) (B : ℕ) : Finset ℕ :=
  {p ∈ P | (p : ℝ) * Q₀ < (B : ℝ)}

theorem maskedActivePrimes_subset (Q₀ : ℝ) (P : Finset ℕ) (B : ℕ) :
    maskedActivePrimes Q₀ P B ⊆ P := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- On masked support below `B`, every designated final divisor is automatically active. -/
theorem primeFactorsIn_maskedActivePrimes_eq
    {Q₀ : ℝ} {P₀ P : Finset ℕ} {B n : ℕ}
    (hP₀prime : ∀ q ∈ P₀, q.Prime)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hdisj : Disjoint P₀ P)
    (hP₀lower : ∀ q ∈ P₀, Q₀ < (q : ℝ))
    (hnpos : 0 < n) (hnB : n ≤ B) (hmask : primeFactorsIn P₀ n ≠ ∅) :
    primeFactorsIn (maskedActivePrimes Q₀ P B) n = primeFactorsIn P n := by
  classical
  apply Finset.ext
  intro p
  simp only [mem_primeFactorsIn, maskedActivePrimes, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hpP, _⟩, hpn⟩
    exact ⟨hpP, hpn⟩
  · rintro ⟨hpP, hpn⟩
    have hmask' : (primeFactorsIn P₀ n).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hmask
    obtain ⟨q, hqfac⟩ := hmask'
    have hq := (mem_primeFactorsIn.mp hqfac)
    have hpPrime := hPprime p hpP
    have hqPrime := hP₀prime q hq.1
    have hpNeq : p ≠ q := by
      intro hpq
      subst q
      exact (Finset.disjoint_left.mp hdisj hq.1) hpP
    have hpNotDvdQ : ¬p ∣ q := by
      intro hpq
      rcases (Nat.dvd_prime hqPrime).mp hpq with hpOne | hpEq
      · exact hpPrime.ne_one hpOne
      · exact hpNeq hpEq
    have hpqCoprime : p.Coprime q := hpPrime.coprime_iff_not_dvd.mpr hpNotDvdQ
    have hpqDvd : p * q ∣ n :=
      hpqCoprime.mul_dvd_of_dvd_of_dvd hpn hq.2
    have hpqLe : p * q ≤ n := Nat.le_of_dvd hnpos hpqDvd
    have hpqB : p * q ≤ B := hpqLe.trans hnB
    have hactive : (p : ℝ) * Q₀ < (B : ℝ) := by
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hmul : (p : ℝ) * Q₀ < (p : ℝ) * (q : ℝ) :=
        mul_lt_mul_of_pos_left (hP₀lower q hq.1) hp0
      exact hmul.trans_le (by exact_mod_cast hpqB)
    exact ⟨⟨hpP, hactive⟩, hpn⟩

/-- The active and full final rough remainders agree coefficientwise after initial masking. -/
theorem logPoly_harmonicNonRoughMoebius_activeRough_eq
    {Q₀ : ℝ} {P₀ P s : Finset ℕ} {B : ℕ}
    (hP₀prime : ∀ q ∈ P₀, q.Prime)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hdisj : Disjoint P₀ P)
    (hP₀lower : ∀ q ∈ P₀, Q₀ < (q : ℝ))
    (hspos : ∀ n ∈ s, 0 < n) (hsB : ∀ n ∈ s, n ≤ B) (w : ℝ) :
    logPoly (harmonicNonRoughMoebiusC P₀)
        {n ∈ s | primeFactorsIn (maskedActivePrimes Q₀ P B) n = ∅} w =
      logPoly (harmonicNonRoughMoebiusC P₀)
        {n ∈ s | primeFactorsIn P n = ∅} w := by
  classical
  rw [logPoly, logPoly, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hmask : primeFactorsIn P₀ n = ∅
  · simp [harmonicNonRoughMoebiusC, hmask]
  · rw [primeFactorsIn_maskedActivePrimes_eq hP₀prime hPprime hdisj hP₀lower
      (hspos n hn) (hsB n hn) hmask]

end

end RHTower.Sieve
