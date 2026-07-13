import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-!
# Multi-telescoping: intersection of coprime principal ideals is their product

The all-depth pair-face completeness proof relies on a purely algebraic identity — "no analytic or
Galois input enters this lemma": on a single transverse orbit the coefficient module is a Laurent
polynomial ring, the kernel of the `i`-th orbit-sum pushforward is the principal ideal `(u_i - 1)`,
and the transverse coboundary claim is

  `⋂_i (u_i - 1) = (∏_i (u_i - 1))`

because the `u_i - 1` are pairwise non-associate primes in that unique factorization domain.  Freed of
its ring, the content is the following: for pairwise relatively prime elements the intersection of the
principal ideals they generate is the principal ideal of their product.  Non-associate primes are
relatively prime, so the concrete lemma follows.
-/

namespace GaloisForLFunctions.TelescopeIdeal

open Finset

variable {R : Type*} [CommRing R]

/-- **Multi-telescoping ideal identity.**  For pairwise relatively prime elements indexed by a finite
set, the intersection of the principal ideals they generate equals the principal ideal of their
product. -/
theorem iInf_span_singleton_eq_span_prod [DecompositionMonoid R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → R)
    (h : (s : Set ι).Pairwise fun i j => IsRelPrime (a i) (a j)) :
    (⨅ i ∈ s, Ideal.span ({a i} : Set R)) = Ideal.span {∏ i ∈ s, a i} := by
  ext x
  simp only [Submodule.mem_iInf, Ideal.mem_span_singleton]
  constructor
  · intro hx
    exact Finset.prod_dvd_of_isRelPrime h (fun i hi => hx i hi)
  · intro hx i hi
    exact dvd_trans (Finset.dvd_prod_of_mem a hi) hx

/-- Two non-associate primes are relatively prime: any common divisor is a unit. -/
theorem isRelPrime_of_prime_of_not_associated [IsDomain R] {p q : R} (hp : Prime p) (hq : Prime q)
    (hpq : ¬ Associated p q) : IsRelPrime p q := by
  intro d hdp hdq
  by_contra hd
  obtain ⟨e, he⟩ := hdp
  rcases hp.irreducible.isUnit_or_isUnit he with hu | hu
  · exact hd hu
  · -- `e` is a unit, so `d` is associate to `p`; then `p ∣ d ∣ q`, forcing `Associated p q`.
    apply hpq
    have hdp' : Associated d p := ⟨hu.unit, by rw [IsUnit.unit_spec]; exact he.symm⟩
    exact hp.associated_of_dvd hq (hdp'.symm.dvd.trans hdq)

/-- The telescoping identity for pairwise non-associate primes — the exact hypothesis form of the
Laurent-ring lemma (the `u_i - 1` are pairwise non-associate primes). -/
theorem iInf_span_singleton_eq_span_prod_of_primes [IsDomain R] [DecompositionMonoid R]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → R) (hprime : ∀ i ∈ s, Prime (a i))
    (hdistinct : (s : Set ι).Pairwise fun i j => ¬ Associated (a i) (a j)) :
    (⨅ i ∈ s, Ideal.span ({a i} : Set R)) = Ideal.span {∏ i ∈ s, a i} := by
  refine iInf_span_singleton_eq_span_prod s a ?_
  intro i hi j hj hij
  exact isRelPrime_of_prime_of_not_associated (hprime i hi) (hprime j hj) (hdistinct hi hj hij)

end GaloisForLFunctions.TelescopeIdeal
