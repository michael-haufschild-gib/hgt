import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite

/-! A maximal proper subgroup of a finite abelian group has prime index. -/

namespace GlobalTheory.Reciprocity

theorem prime_card_quotient_of_isCoatom {G : Type*} [CommGroup G]
    (H : Subgroup G) (hH : IsCoatom H) : (Nat.card (G ⧸ H)).Prime := by
  let q := QuotientGroup.mk' H
  have hq := QuotientGroup.mk'_surjective H
  letI : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH.ne_top
  apply CommGroup.is_simple_iff_prime_card.mp
  constructor
  intro A _
  have hle : H ≤ A.comap q := by
    intro x hx
    have h1 : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    change q x ∈ A
    rw [h1]
    exact one_mem _
  by_cases he : A.comap q = H
  · left
    rw [← Subgroup.map_comap_eq_self_of_surjective hq A, he, QuotientGroup.map_mk'_self]
  · right
    have ht := (hH.ne_iff_eq_top hle).mp he
    rw [← Subgroup.map_comap_eq_self_of_surjective hq A, ht, Subgroup.map_top_of_surjective _ hq]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.prime_card_quotient_of_isCoatom
