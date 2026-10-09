import GaloisForLFunctions.HTGeometry.PaperGenericSL2Presentation
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Unique factorization in the native generic SL₂ torsor

The source determinant theorem gives unique factorization after adjoining one
variable. Constant polynomials preserve irreducibility, so primality descends
to the original torsor. Noetherianity supplies termination of factorization.
-/

namespace GaloisForLFunctions.HTGeometry

private theorem nativeSL2_irreducible_C {a : genericSL ℂ 2} (ha : Irreducible a) :
    Irreducible (Polynomial.C a) where
  not_isUnit h := ha.not_isUnit (Polynomial.isUnit_C.mp h)
  isUnit_or_isUnit {p q} hpq := by
    have hc : (Polynomial.C a : Polynomial (genericSL ℂ 2)) ≠ 0 := by
      simpa using ha.ne_zero
    have hp : p ≠ 0 := by
      intro h
      apply hc
      simpa [h] using hpq
    have hq : q ≠ 0 := by
      intro h
      apply hc
      simpa [h] using hpq
    have hd : p.natDegree + q.natDegree = 0 := by
      rw [← Polynomial.natDegree_mul hp hq, ← hpq, Polynomial.natDegree_C]
    have hpC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.add_eq_zero_iff.mp hd).1
    have hqC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.add_eq_zero_iff.mp hd).2
    have ha' : a = p.coeff 0 * q.coeff 0 := by
      apply Polynomial.C_injective
      rw [map_mul, ← hpC, ← hqC]
      exact hpq
    rcases ha.isUnit_or_isUnit ha' with h | h
    · left
      rw [hpC]
      exact Polynomial.isUnit_C.mpr h
    · right
      rw [hqC]
      exact Polynomial.isUnit_C.mpr h

/-- Unique factorization holds in the existing generic SL₂ coordinate algebra itself. -/
instance paperGenericSL2UFD : UniqueFactorizationMonoid (genericSL ℂ 2) where
  irreducible_iff_prime := by
    intro a
    exact ⟨fun ha => Polynomial.prime_C_iff.mp (nativeSL2_irreducible_C ha).prime,
      fun ha => ha.irreducible⟩

end GaloisForLFunctions.HTGeometry
