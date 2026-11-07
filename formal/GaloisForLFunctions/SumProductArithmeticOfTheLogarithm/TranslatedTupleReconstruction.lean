import GaloisForLFunctions.HTGeometry.StandardRationalExpansion
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots

/-!
# A tuple is determined by its translated products

A multiset of `k` natural numbers is determined by its cardinality and
the products of its translates by `0,...,k-1`. The product polynomial
is monic of degree `k`, so the difference of two such polynomials has
degree below `k`. This holds at every degree, without a Taylor approximation.
-/

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Finset Polynomial

private theorem shiftPoly_eq_ofMultiset (l : Multiset ℕ) :
    shiftPoly l = Polynomial.ofMultiset (l.map fun n : ℕ => -(n : ℂ)) := by
  simp only [shiftPoly, Polynomial.ofMultiset_apply, Multiset.map_map,
    Function.comp_def, map_neg, sub_neg_eq_add]

/-- The translated product polynomial remembers every entry and its multiplicity. -/
theorem shiftPoly_injective : Function.Injective shiftPoly := by
  intro l m h
  rw [shiftPoly_eq_ofMultiset, shiftPoly_eq_ofMultiset] at h
  have hm := Polynomial.ofMultiset_injective ℂ h
  apply Multiset.map_injective (f := fun n : ℕ => -(n : ℂ)) ?_ hm
  intro a b hab
  exact_mod_cast neg_injective hab

/-- Any `k` distinct translation parameters recover a tuple of cardinality `k`. -/
theorem eq_of_shifted_products (l m : Multiset ℕ) (H : Finset ℂ)
    (hcard : l.card = m.card) (hH : l.card ≤ H.card)
    (heval : ∀ z ∈ H, shiftProd l z = shiftProd m z) : l = m := by
  apply shiftPoly_injective
  apply Polynomial.eq_of_degree_le_of_eval_finset_eq H
  · rw [Polynomial.degree_eq_natDegree (shiftPoly_monic l).ne_zero,
      shiftPoly_natDegree]
    exact_mod_cast hH
  · rw [Polynomial.degree_eq_natDegree (shiftPoly_monic l).ne_zero,
      Polynomial.degree_eq_natDegree (shiftPoly_monic m).ne_zero,
      shiftPoly_natDegree, shiftPoly_natDegree, hcard]
  · rw [(shiftPoly_monic l).leadingCoeff, (shiftPoly_monic m).leadingCoeff]
  · simpa only [shiftPoly_eval] using heval

/-- The cardinality and the first `k` translated products are a complete invariant. -/
theorem translated_products_complete (l m : Multiset ℕ) :
    (l.card = m.card ∧ ∀ j : ℕ, j < l.card → shiftProd l j = shiftProd m j) ↔ l = m := by
  constructor
  · rintro ⟨hc, hv⟩
    apply eq_of_shifted_products l m ((range l.card).image fun j : ℕ => (j : ℂ)) hc
    · rw [card_image_of_injective _ Nat.cast_injective, card_range]
    · intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
      exact hv j (mem_range.mp hj)
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
