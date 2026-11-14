import GaloisForLFunctions.HTGeometry.FamilyBuildingFree
import GaloisForLFunctions.HTGeometry.BuildingVanishingDual
import GaloisForLFunctions.HTGeometry.BuildingAutomorphismAction

/-!
# The Steinberg module is free

The lattice of subspaces of a finite-dimensional vector space is modular, and every nonzero subspace
contains a line while every proper subspace lies in a hyperplane, so the freeness theorem for a
disjoint union of interval buildings applies to it in both orders.  In every degree the homology of
the building of a vector space is therefore a coproduct of copies of the coefficients — in degree
zero because homology in degree zero is the coproduct over the components, and above it by the
Mayer--Vietoris descent.

In particular the Steinberg module, the top homology, is free.  That is the module-theoretic half of
Solomon's theorem; the identification of a basis with the apartment classes is not asserted here.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u c

section

variable {K V : Type u} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

omit [FiniteDimensional K V] in
/-- **The homology of the building of a vector space is free in every degree.** -/
theorem isFreeOver_homology_properPart_submodule [Nontrivial V] (R : C) (i : ℕ) :
    IsFreeOver.{v, c, u} R ((nerve (properPart (Submodule K V))).homology R i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact isFreeOver_homology_zero _ R
  · exact isFreeOver_homology_properPart
      (fun U hU => (eq_bot_or_exists_atom_le U).resolve_left (ne_of_gt hU)) R i hi bot_lt_top

/-- **The same on the dual lattice**, the order in which the horizon complex presents it. -/
theorem isFreeOver_homology_properPart_submodule_dual [Nontrivial V] (R : C) (i : ℕ) :
    IsFreeOver.{v, c, u} R ((nerve (properPart (Submodule K V)ᵒᵈ)).homology R i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact isFreeOver_homology_zero _ R
  · refine isFreeOver_homology_properPart (fun U hU => ?_) R i hi bot_lt_top
    obtain ⟨H, hH, hUH⟩ :=
      (eq_top_or_exists_le_coatom (OrderDual.ofDual U : Submodule K V)).resolve_left
        (ne_of_lt hU)
    exact ⟨OrderDual.toDual H, hH.dual, hUH⟩

/-- **The homology of the horizon complex is free in every degree.** -/
theorem isFreeOver_homology_properPart_submodule_orderDual [Nontrivial V] (R : C) (i : ℕ) :
    IsFreeOver.{v, c, u} R ((nerve ((properPart (Submodule K V))ᵒᵈ)).homology R i) :=
  IsFreeOver.of_iso (isFreeOver_homology_properPart_submodule_dual R i)
    ((SSet.homologyFunctor R i).mapIso
      (orderIsoNerveIso (properPartDualOrderIso (L := Submodule K V))).symm)

/-- **The homology of the building, in the presentation of the horizon complex, is free.** -/
theorem isFreeOver_homology_building [Nontrivial V] (R : C) (i : ℕ) :
    IsFreeOver.{v, c, u} R ((nerveFunctor.obj
      (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)).homology R i) :=
  IsFreeOver.of_iso (isFreeOver_homology_properPart_submodule_orderDual (K := K) (V := V) R i)
    ((SSet.homologyFunctor R i).mapIso
      (orderIsoNerveIso (OrderIso.dual (properPartNeOrderIso (L := Submodule K V)))).symm)

end

namespace Steinberg

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

omit [FiniteDimensional K V] in
/-- **The Steinberg module is free.**  The top homology of the building of a finite-dimensional
vector space is a coproduct of copies of the coefficients. -/
theorem isFreeOver_steinbergModule [Nontrivial V] (R : C) :
    IsFreeOver.{v, c, u} R (steinbergModule K V R) :=
  isFreeOver_homology_properPart_submodule R (finrank K V - 2)

end Steinberg

end GaloisForLFunctions.HTGeometry
