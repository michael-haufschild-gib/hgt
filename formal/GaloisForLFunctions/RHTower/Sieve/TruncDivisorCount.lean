import GaloisForLFunctions.RHTower.Sieve.BrunPure
import GaloisForLFunctions.RHTower.Sieve.Mertens

/-!
# Counting the Brun-truncated divisors of a primorial

The sieve error of every Chernoff tail in this folder is the number of divisors of `z#` retained by
a Brun truncation at `r` prime factors.  It is bounded with no combinatorics at all: such a divisor
is squarefree, all its prime factors are at most `z`, and it has at most `r` of them, so it is at
most `z^r`.  Distinct divisors are distinct integers in `[1, z^r]`, whence

    #{d ∣ z# : ω d ≤ r}  ≤  z^r.

That is the input the deviation bounds need in order to be turned into an explicit negative power of
`log z`: it says the sieve error is subpolynomial as soon as `z^r` is.
-/

namespace RHTower.Sieve

open Finset

/-- A Brun-truncated divisor of a primorial is at most `z ^ r`. -/
theorem le_pow_of_mem_truncDivisors_primorial {z r d : ℕ} (hz : 1 ≤ z)
    (hd : d ∈ truncDivisors (primorial z) r) : d ≤ z ^ r := by
  classical
  rw [mem_truncDivisors] at hd
  obtain ⟨⟨hdvd, hne⟩, homega⟩ := hd
  have hsf : Squarefree d := (squarefree_primorial z).squarefree_of_dvd hdvd
  have hfac : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsf
  have hsub : d.primeFactors ⊆ (primorial z).primeFactors := Nat.primeFactors_mono hdvd hne
  have hle : ∀ p ∈ d.primeFactors, p ≤ z := by
    intro p hp
    have hp' : p ∈ (primorial z).primeFactors := hsub hp
    rw [primeFactors_primorial_eq, Nat.mem_primesLE] at hp'
    exact hp'.1
  have hprod : ∏ p ∈ d.primeFactors, p ≤ z ^ d.primeFactors.card :=
    Finset.prod_le_pow_card _ _ _ hle
  have hpow : z ^ d.primeFactors.card ≤ z ^ r := Nat.pow_le_pow_right hz homega
  rw [hfac] at hprod
  exact le_trans hprod hpow

/-- **The Brun-truncated divisor count of a primorial.** -/
theorem card_truncDivisors_primorial_le (z r : ℕ) (hz : 1 ≤ z) :
    (truncDivisors (primorial z) r).card ≤ z ^ r := by
  classical
  have hsub : truncDivisors (primorial z) r ⊆ Finset.Icc 1 (z ^ r) := by
    intro d hd
    have hle := le_pow_of_mem_truncDivisors_primorial hz hd
    rw [mem_truncDivisors] at hd
    obtain ⟨⟨hdvd, hne⟩, -⟩ := hd
    have hd0 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by
      rintro rfl
      exact hne (Nat.eq_zero_of_zero_dvd hdvd))
    rw [Finset.mem_Icc]
    exact ⟨hd0, hle⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Nat.card_Icc]
  omega

end RHTower.Sieve
