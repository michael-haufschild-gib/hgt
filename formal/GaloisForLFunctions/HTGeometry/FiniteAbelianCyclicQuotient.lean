import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Order.Atoms.Finite

/-!
# Nontrivial finite abelian groups have nontrivial cyclic quotients

A maximal proper subgroup of a finite abelian group is normal.  Any element outside it generates
the quotient, because adjoining that element to the maximal subgroup gives the whole group.  This
is the exact group-theoretic reduction used when a nontrivial connected finite cover has abelian
monodromy: it admits a nontrivial cyclic intermediate cover.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {A : Type u} [CommGroup A]

/-- A coatom in the subgroup lattice of an abelian group has cyclic quotient. -/
theorem isCyclic_quotient_of_isCoatom (N : Subgroup A) (hN : IsCoatom N) :
    IsCyclic (A ⨸ N) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt hN.lt_top
  refine ⟨QuotientGroup.mk' N g, ?_⟩
  have hsup : N ⊔ Subgroup.zpowers g = ⊤ := by
    apply (hN.ne_iff_eq_top le_sup_left).mp
    intro h
    have : g ∈ N ⊔ Subgroup.zpowers g := le_sup_right (Subgroup.mem_zpowers g)
    rw [h] at this
    exact hg this
  have hmap := congrArg (fun H : Subgroup A ↦ H.map (QuotientGroup.mk' N)) hsup
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup,
    MonoidHom.map_zpowers, Subgroup.map_top, QuotientGroup.range_mk'] at hmap
  exact hmap

/-- Every nontrivial finite abelian group has a maximal proper subgroup and hence a nontrivial
cyclic quotient. -/
theorem exists_nontrivial_cyclic_quotient [Finite A] [Nontrivial A] :
    ∃ N : Subgroup A, IsCoatom N ∧ IsCyclic (A ⨸ N) ∧ Nontrivial (A ⨸ N) := by
  letI : Finite (Subgroup A) :=
    Finite.of_injective (fun N : Subgroup A ↦ (N : Set A)) SetLike.coe_injective
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Subgroup A)
  refine ⟨N, hN, isCyclic_quotient_of_isCoatom N hN, ?_⟩
  exact QuotientGroup.nontrivial_iff.mpr hN.ne_top

end GaloisForLFunctions.HTGeometry
