import GaloisForLFunctions.HTGeometry.BuildingHomologyConcentration

/-!
# The all-depth cusped complex has the building's concentrated homology

The cusps are contractible rays attached to the depth-one vertices, so the all-depth order complex
deformation-retracts to the building and has its homology in every degree — that retraction is
already formalized.  With the Solomon--Tits vanishing now available, the consequence is immediate:
the homology of the all-depth complex vanishes in every positive degree except `N - 2`, even though
the complex itself is infinite dimensional.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

section

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [DecidableEq (Submodule K V)]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- **The all-depth cusped horizon complex has no homology in positive degrees except the top
one.**  Adding an infinite private tail to every elementary horizon changes nothing: the cusps
retract away, and what is left is the building, whose homology is concentrated. -/
theorem isZero_cuspHomology_of_ne [Nontrivial V] (R : C) (i : ℕ) (hi : 1 ≤ i)
    (hne : i ≠ finrank K V - 2) :
    Limits.IsZero ((nerveFunctor.obj (Cat.of (CuspedVertex K V))).homology R i) :=
  Limits.IsZero.of_iso (isZero_homology_building_of_ne R i hi hne)
    (cuspBuildingHomologyIso K V R i)

end

end GaloisForLFunctions.HTGeometry
