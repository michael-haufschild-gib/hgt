import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Roots

/-!
# Elementary symmetric functions determine a multiset

The Prouhet–Tarry–Escott step used across the polynomial-Taylor phase-lock cards is that two
`D`-element offset multisets whose symmetric data agree must be equal.  Freed of its analytic
wrapper: over an integral domain, two multisets of the same cardinality with equal elementary
symmetric functions are equal, because they are the root multisets of the monic polynomials
`∏ (X - aᵢ)` whose coefficients are those symmetric functions.
-/

open Polynomial Multiset

namespace GaloisForLFunctions

/-- Two multisets of equal cardinality over an integral domain with the same elementary symmetric
functions are equal. -/
theorem multiset_eq_of_esymm_eq {R : Type*} [CommRing R] [IsDomain R] {s t : Multiset R}
    (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ k ≤ Multiset.card s, s.esymm k = t.esymm k) : s = t := by
  have hpoly : (s.map fun a => X - C a).prod = (t.map fun a => X - C a).prod := by
    ext k
    by_cases hk : k ≤ Multiset.card s
    · have hk' : k ≤ Multiset.card t := hcard ▸ hk
      rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t hk',
        h (Multiset.card s - k) (Nat.sub_le _ _), hcard]
    · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
  have hroots := congrArg Polynomial.roots hpoly
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hroots

end GaloisForLFunctions
