import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A cyclic group has one subgroup of each order

In a finite cyclic group a subgroup of order `d` consists exactly of the solutions of `x ^ d = 1`,
because it is contained in that set and the set has at most `d` elements.

So two subgroups of the same order coincide, which is the uniqueness of the quadratic subextension
of a cyclic extension.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Classical

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G] [IsCyclic G]

/-- **A subgroup of a cyclic group is its own torsion set.** -/
theorem subgroup_toFinset_eq_filter (H : Subgroup G) :
    (H : Set G).toFinset = Finset.univ.filter (fun a : G => a ^ Fintype.card H = 1) := by
  have hle : (H : Set G).toFinset ⊆
      Finset.univ.filter (fun a : G => a ^ Fintype.card H = 1) := by
    intro x hx
    rw [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    have hpow : (⟨x, hx⟩ : H) ^ Fintype.card H = 1 := pow_card_eq_one
    exact congrArg Subtype.val hpow
  refine Finset.eq_of_subset_of_card_le hle ?_
  have hcard : (H : Set G).toFinset.card = Fintype.card H := by
    simp
  rw [hcard]
  exact IsCyclic.card_pow_eq_one_le Fintype.card_pos

/-- **Two subgroups of a cyclic group with the same order are equal.** -/
theorem subgroup_eq_of_card_eq {H K : Subgroup G}
    (h : Fintype.card H = Fintype.card K) : H = K := by
  have h1 := subgroup_toFinset_eq_filter H
  have h2 := subgroup_toFinset_eq_filter K
  rw [h] at h1
  have hfin : (H : Set G).toFinset = (K : Set G).toFinset := by rw [h1, h2]
  exact SetLike.ext' (Set.toFinset_inj.mp hfin)

end GaloisForLFunctions.HTGeometry
