import GaloisForLFunctions.HTGeometry.SquarefreeOrderedFactorization
import Mathlib.Data.ZMod.QuotientRing

/-!
# CRT infrastructure for distinct prime families

The existing `DistinctPrimeFamily` stores a labelled injective family of certified primes.  This
module supplies its pairwise-coprime certificate, nonzero product modulus, and canonical
simultaneous Chinese-remainder equivalence.
-/

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes
namespace DistinctPrimeFamily

/-- Distinct certified prime values are pairwise coprime. -/
theorem pairwise_coprime {k : ℕ} (P : DistinctPrimeFamily k) :
    Pairwise (fun i j => Nat.Coprime (P.primeValue i) (P.primeValue j)) := by
  intro i j hij
  exact (Nat.coprime_primes (P.prime i) (P.prime j)).mpr
    (fun h => hij (P.injective h))

/-- Product modulus of a distinct prime family is nonzero, including the empty product. -/
instance product_neZero {k : ℕ} (P : DistinctPrimeFamily k) : NeZero P.product :=
  ⟨by
    rw [product]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (P.prime i).ne_zero⟩

/-- Canonical CRT equivalence for a labelled distinct-prime product. -/
noncomputable def crtEquiv {k : ℕ} (P : DistinctPrimeFamily k) :
    ZMod P.product ≃+* (∀ i, ZMod (P.primeValue i)) :=
  ZMod.prodEquivPi P.primeValue P.pairwise_coprime

end DistinctPrimeFamily
end GaloisForLFunctions.IrregularStokes
