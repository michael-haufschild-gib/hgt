import GaloisForLFunctions.RHTower.Sieve.PrimePowerFactorialEnergy
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Sym.Card

/-!
# A multiset lower bound for smooth integers

Distinct multisets of primes have distinct products. Multisets of size `r`
over primes below `N` therefore give `multichoose (π(N)) r` smooth integers
at most `N^r`. This is the counting mechanism in Zhang, Proposition 3.1,
*Square-root logarithmic bounds for the arithmetic complexity of factorial multiples*.
-/

namespace RHTower.Sieve

open Finset

private def cutoffPrime (N : ℕ) (p : N.primesBelow) : CertifiedPrime :=
  ⟨p.1, (Nat.mem_primesBelow.mp p.2).2⟩

private theorem cutoffPrime_injective (N : ℕ) : Function.Injective (cutoffPrime N) := by
  intro p q hpq
  exact Subtype.ext (congrArg Subtype.val hpq)

/-- Product of a multiset chosen from the primes below a fixed cutoff. -/
def cutoffPrimeProduct (N : ℕ) (s : Multiset N.primesBelow) : ℕ :=
  primeMultisetProduct (s.map (cutoffPrime N))

/-- Unique factorization recovers the entire bounded prime multiset. -/
theorem cutoffPrimeProduct_injective (N : ℕ) : Function.Injective (cutoffPrimeProduct N) := by
  intro s t h
  exact Multiset.map_injective (cutoffPrime_injective N)
    (primeMultisetProduct_injective h)

/-- A multiset product stays smooth and below the corresponding power of its cutoff. -/
theorem cutoffPrimeProduct_bounds (N : ℕ) (s : Multiset N.primesBelow) :
    cutoffPrimeProduct N s ∈ N.smoothNumbers ∧
      cutoffPrimeProduct N s ≤ N ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [cutoffPrimeProduct, primeMultisetProduct, Nat.mem_smoothNumbers]
  | @cons p s ih =>
      have hp := Nat.mem_primesBelow.mp p.2
      have hpSmooth : (p : ℕ) ∈ N.smoothNumbers := by
        simp [Nat.mem_smoothNumbers, hp.2.ne_zero, hp.2.primeFactorsList, hp.1]
      have hcons : cutoffPrimeProduct N (p ::ₘ s) = (p : ℕ) * cutoffPrimeProduct N s := by
        simp [cutoffPrimeProduct, primeMultisetProduct, cutoffPrime]
      rw [hcons, Multiset.card_cons, pow_succ]
      exact ⟨Nat.mul_mem_smoothNumbers hpSmooth ih.1,
        (Nat.mul_le_mul hp.1.le ih.2).trans_eq (Nat.mul_comm _ _)⟩

/-- The smooth count contains every multiset of `r` primes below `N`. -/
theorem multichoose_primesBelow_le_smoothNumbersUpTo (N r : ℕ) :
    N.primesBelow.card.multichoose r ≤ (Nat.smoothNumbersUpTo (N ^ r) N).card := by
  let f : Sym N.primesBelow r → Nat.smoothNumbersUpTo (N ^ r) N := fun s =>
    ⟨cutoffPrimeProduct N s.1, Nat.mem_smoothNumbersUpTo.mpr
      ⟨s.2 ▸ (cutoffPrimeProduct_bounds N s.1).2, (cutoffPrimeProduct_bounds N s.1).1⟩⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact cutoffPrimeProduct_injective N (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Sym.card_sym_eq_multichoose, Fintype.card_coe] using h

#print axioms multichoose_primesBelow_le_smoothNumbersUpTo

end RHTower.Sieve
