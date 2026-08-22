import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

/-!
# A squarefree non-unit is not a square in the fraction field

Kummer independence of a family of discriminants is, in the cases that arise from an explicit
polynomial family, a statement about unique factorisation: no nonempty sub-product of the
discriminants has every prime to an even multiplicity.  The bridge from that combinatorial fact to
"not a square in the fraction field" is the following: a unique factorisation domain is integrally
closed, so a square root of a ring element that lies in the fraction field already lies in the
ring, and a squarefree element with a square root in the ring is a unit.

## Main results

* `isSquare_of_isSquare_algebraMap` — a ring element that is a square in the fraction field is a
  square in the ring.
* `not_isSquare_algebraMap_of_squarefree` — hence a squarefree non-unit is not a square there.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- A ring element that becomes a square in the fraction field is already a square in the ring,
because a unique factorisation domain is integrally closed. -/
theorem isSquare_of_isSquare_algebraMap {r : R} (h : IsSquare (algebraMap R K r)) :
    IsSquare r := by
  obtain ⟨x, hx⟩ := h
  have hint : IsIntegral R x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C r, Polynomial.monic_X_pow_sub_C r (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [pow_two, ← hx]
    ring
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, hy, ← hx]

omit [IsDomain R] in
/-- **A squarefree non-unit is not a square in the fraction field.** -/
theorem not_isSquare_algebraMap_of_squarefree {r : R} (hsf : Squarefree r) (hnu : ¬ IsUnit r) :
    ¬ IsSquare (algebraMap R K r) := by
  intro h
  obtain ⟨y, hy⟩ := isSquare_of_isSquare_algebraMap (K := K) h
  exact hnu (by rw [hy]; exact (hsf y (by rw [hy])).mul (hsf y (by rw [hy])))

end GaloisForLFunctions.HTGeometry
