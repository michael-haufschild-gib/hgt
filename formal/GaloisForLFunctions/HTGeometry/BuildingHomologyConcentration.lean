import GaloisForLFunctions.HTGeometry.BuildingVanishingDual
import GaloisForLFunctions.HTGeometry.CuspedHorizonHomotopy

/-!
# The homology of the building is concentrated in one degree

Two vanishing statements meet.  Below the top degree the Solomon--Tits induction gives vanishing;
above it the order complex simply has no simplices, because a strict chain of proper nonzero
subspaces has at most `N - 1` members.  Together: in positive degrees the homology of the building
vanishes except possibly in degree `N - 2`.

That is the homological content of the statement that the building is a wedge of `(N-2)`-spheres —
the part of it that does not mention homotopy types.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u c

section

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {C : Type c} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The homology of the building vanishes in every positive degree but the top one.** -/
theorem isZero_homology_building_of_ne [Nontrivial V] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hne : i ≠ finrank K V - 2) :
    Limits.IsZero ((nerveFunctor.obj
      (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)).homology R i) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hrank : i + 3 ≤ finrank K V := by
      have hpos : 0 < finrank K V := finrank_pos
      omega
    have hzero := isZero_homology_properPart_submodule_orderDual (K := K) (V := V) R i hi hrank
    exact Limits.IsZero.of_iso hzero
      ((SSet.homologyFunctor R i).mapIso
        (orderIsoNerveIso (OrderIso.dual (properPartNeOrderIso (L := Submodule K V)))).symm)
  · haveI := buildingHasDimensionLT K V
    exact isZero_homology_of_hasDimensionLT _ (finrank K V - 1) R i (by omega)

end

end GaloisForLFunctions.HTGeometry
