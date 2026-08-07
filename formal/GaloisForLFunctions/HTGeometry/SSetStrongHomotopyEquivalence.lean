import GaloisForLFunctions.HTGeometry.NerveHomotopy

/-!
# Strong homotopy equivalences of simplicial sets

`SSet.Homotopy` is directed: for an arbitrary, non-Kan target it does not carry a symmetry or a
transitivity operation.  A homotopy equivalence nevertheless has a completely unambiguous direct
form: two maps together with a homotopy from each identity to the corresponding composite.

This module records that structure and shows that every strong deformation retract constructed in
`NerveHomotopy` supplies one.  Thus a deformation retract can be used as an actual statement about
simplicial homotopy types, independently of the homology functor.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

universe u

/-- A direct strong homotopy equivalence between simplicial sets.  The orientations of the two
homotopies agree with `SSet.Homotopy`: each runs from an identity to a composite. -/
structure SSetStrongHomotopyEquiv (X Y : SSet.{u}) where
  /-- Forward map. -/
  hom : X ⟶ Y
  /-- Homotopy inverse. -/
  inv : Y ⟶ X
  /-- The forward map followed by its inverse is homotopic to the identity of the source. -/
  hom_inv_homotopy : SSet.Homotopy (𝟙 X) (hom ≫ inv)
  /-- The inverse followed by the forward map is homotopic to the identity of the target. -/
  inv_hom_homotopy : SSet.Homotopy (𝟙 Y) (inv ≫ hom)

/-- An isomorphism of simplicial sets is a strong homotopy equivalence. -/
noncomputable def SSetStrongHomotopyEquiv.ofIso {X Y : SSet.{u}} (e : X ≅ Y) :
    SSetStrongHomotopyEquiv X Y where
  hom := e.hom
  inv := e.inv
  hom_inv_homotopy := by
    rw [e.hom_inv_id]
    exact SSet.RelativeMorphism.Homotopy.refl _
  inv_hom_homotopy := by
    rw [e.inv_hom_id]
    exact SSet.RelativeMorphism.Homotopy.refl _

/-- A strong deformation retract is, without applying any invariant, a strong homotopy
equivalence of simplicial sets. -/
noncomputable def SSetDeformationRetract.toStrongHomotopyEquiv {X Y : SSet.{u}}
    (d : SSetDeformationRetract X Y) : SSetStrongHomotopyEquiv X Y where
  hom := d.retr
  inv := d.incl
  hom_inv_homotopy := d.homotopy
  inv_hom_homotopy := by
    rw [d.incl_retr]
    exact SSet.RelativeMorphism.Homotopy.refl _

end GaloisForLFunctions.HTGeometry
