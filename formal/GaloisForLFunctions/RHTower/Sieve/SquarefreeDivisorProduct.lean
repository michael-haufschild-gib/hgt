import Mathlib
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.SelbergBounds

/-!
# Sums over the divisors of a product of distinct primes

The divisors of a squarefree modulus are exactly the sub-products of its prime factors, so a sum of
a "multiplicative-in-the-prime-factors" quantity over them is an Euler product.  This is the
identity every sieve bounding sum reduces to once the modulus is squarefree.
-/

namespace RHTower.Sieve

open Finset

/-- **Divisors of a product of distinct primes are indexed by subsets.** -/
theorem sum_divisors_prod_primes_eq {M : Type*} [AddCommMonoid M] {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (F : ℕ → M) :
    ∑ l ∈ (∏ p ∈ s, p).divisors, F l = ∑ t ∈ s.powerset, F (∏ p ∈ t, p) := by
  classical
  have hP0 : (∏ p ∈ s, p) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
    exact (hs p hp).ne_zero
  refine (Finset.sum_nbij' (fun t => ∏ p ∈ t, p) (fun l => l.primeFactors) ?_ ?_ ?_ ?_ ?_).symm
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact Nat.mem_divisors.2 ⟨Finset.prod_dvd_prod_of_subset _ _ _ ht, hP0⟩
  · intro l hl
    rw [Nat.mem_divisors] at hl
    rw [Finset.mem_powerset]
    intro p hp
    have hpl : p ∣ l := Nat.dvd_of_mem_primeFactors hp
    have hpP : p ∣ ∏ q ∈ s, q := hpl.trans hl.1
    obtain ⟨q, hq, hpq⟩ :=
      (Prime.dvd_finsetProd_iff (Nat.prime_of_mem_primeFactors hp).prime (fun q => q)).1 hpP
    have := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hp) (hs q hq)).1 hpq
    rwa [this]
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => hs p (ht hp)
  · intro l hl
    rw [Nat.mem_divisors] at hl
    have hsq : Squarefree l :=
      Squarefree.squarefree_of_dvd hl.1 (_root_.Sieve.prodDistinctPrimes_squarefree s hs)
    exact Nat.prod_primeFactors_of_squarefree hsq
  · intro t _
    rfl

/-- **The Euler product of a sieve bounding sum over a squarefree modulus.** -/
theorem sum_divisors_prod_primes_eq_prod {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℝ) :
    ∑ l ∈ (∏ p ∈ s, p).divisors, (∏ p ∈ l.primeFactors, a p) = ∏ p ∈ s, (a p + 1) := by
  classical
  rw [sum_divisors_prod_primes_eq hs (fun l => ∏ p ∈ l.primeFactors, a p)]
  have hcongr : ∀ t ∈ s.powerset, (∏ p ∈ (∏ q ∈ t, q).primeFactors, a p) = ∏ p ∈ t, a p := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Nat.primeFactors_prod fun p hp => hs p (ht hp)]
  rw [Finset.sum_congr rfl hcongr, Finset.prod_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

end RHTower.Sieve
