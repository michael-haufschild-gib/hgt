import GaloisForLFunctions.HTGeometry.InverseJetNumerator

/-!
# The inverse jet numerators are natural in the coefficient ring

The numerators of the inverse jet coefficients are built by a recursion whose only ingredients are
the observed coefficients, sums and products.  So a ring map carries the numerators of a jet to the
numerators of the image jet.

This is what lets the fibre's defining system be written over a polynomial ring in the unknown
coefficients and then specialised at a point: the system over the ground field is the image of the
universal one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **The numerators commute with a ring map.** -/
theorem invNumerator_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : ℕ → R) :
    ∀ k : ℕ, (invNumerator u k).map φ = invNumerator (fun i => φ (u i)) k
  | 0 => by rw [invNumerator_zero, invNumerator_zero, Polynomial.map_one]
  | (k + 1) => by
      rw [invNumerator_succ, invNumerator_succ, Polynomial.map_neg, Polynomial.map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : k - i < k + 1 := by omega
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
        Polynomial.map_X, invNumerator_map φ u (k - i)]

/-- **Evaluating the numerators through a ring map.** -/
theorem eval_invNumerator_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : ℕ → R)
    (k : ℕ) (a : R) :
    φ ((invNumerator u k).eval a) = (invNumerator (fun i => φ (u i)) k).eval (φ a) := by
  rw [← invNumerator_map φ u k, Polynomial.eval_map, Polynomial.eval₂_hom]

end GaloisForLFunctions.HTGeometry
