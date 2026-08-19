import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Factoring a polynomial into a constant and monic irreducibles

Over a field every nonzero polynomial is a nonzero constant times a product of monic irreducible
polynomials, and the degrees of those factors add up to its degree.

* `exists_monic_irreducible_factorization` : **the factorization, as a list.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial UniqueFactorizationMonoid

variable {F : Type*} [Field F]

/-- **A nonzero polynomial is a nonzero constant times a list of monic irreducible factors**, whose
degrees add up to its degree. -/
theorem exists_monic_irreducible_factorization {p : Polynomial F} (hp : p ≠ 0) :
    ∃ (c : F) (qs : List (Polynomial F)), c ≠ 0 ∧
      (∀ q ∈ qs, q.Monic ∧ Irreducible q ∧ 1 ≤ q.natDegree) ∧
      p = Polynomial.C c * qs.prod ∧
      (qs.map Polynomial.natDegree).sum = p.natDegree := by
  classical
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hp
  set s : Multiset (Polynomial F) := normalizedFactors p with hs
  set qs : List (Polynomial F) := s.toList with hqs
  have hmemiff : ∀ q, q ∈ qs ↔ q ∈ s := fun q => Multiset.mem_toList
  have hfac : ∀ q ∈ qs, q.Monic ∧ Irreducible q ∧ 1 ≤ q.natDegree := by
    intro q hq
    have hqs' : q ∈ s := (hmemiff q).1 hq
    have hirr : Irreducible q := irreducible_of_normalized_factor q hqs'
    have hnorm : normalize q = q := normalize_normalized_factor q hqs'
    have hq0 : q ≠ 0 := hirr.ne_zero
    have hmonic : q.Monic := by
      have := Polynomial.monic_normalize (p := q) hq0
      rwa [hnorm] at this
    refine ⟨hmonic, hirr, ?_⟩
    by_contra hcon
    have hdeg0 : q.natDegree = 0 := by omega
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 hdeg0
    have ha1 : a = 1 := by
      have : q.leadingCoeff = 1 := hmonic
      rw [← ha] at this
      simpa using this
    rw [ha1, map_one] at ha
    exact hirr.not_isUnit (ha ▸ isUnit_one)
  have hmonicAll : ∀ q ∈ s, q.Monic := fun q hq => (hfac q ((hmemiff q).2 hq)).1
  have hprod : qs.prod = s.prod := Multiset.prod_toList s
  obtain ⟨c, hcu, hCc⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hcne : c ≠ 0 := hcu.ne_zero
  have hpeq : p = Polynomial.C c * qs.prod := by
    rw [hprod, hCc, ← hu]
    ring
  refine ⟨c, qs, hcne, hfac, hpeq, ?_⟩
  have hCcne : (Polynomial.C c : Polynomial F) ≠ 0 := by simpa using hcne
  have hsprod0 : s.prod ≠ 0 := by
    intro hcon
    apply hp
    rw [hpeq, hprod, hcon, mul_zero]
  have hdegp : p.natDegree = s.prod.natDegree := by
    rw [hpeq, hprod, Polynomial.natDegree_mul hCcne hsprod0, Polynomial.natDegree_C, zero_add]
  have hsum : (qs.map Polynomial.natDegree).sum = (Multiset.map Polynomial.natDegree s).sum := by
    conv_rhs => rw [← Multiset.coe_toList s]
    rfl
  rw [hsum, hdegp, Polynomial.natDegree_multiset_prod_of_monic s hmonicAll]

end GaloisForLFunctions.HTGeometry
