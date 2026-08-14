import GaloisForLFunctions.HTGeometry.WedgeFacetLowerBound
import GaloisForLFunctions.HTGeometry.CanonicalConstraintOrientationLimit
import GaloisForLFunctions.HTGeometry.PartialCompletionAdmissionSeparationLaw
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.FittingPresentation

/-!
# Explicit ground models for residual structure interfaces

Several proposition interfaces occur as structure projections.  Constructor-based proofs are
semantically complete but invisible to conclusion-head audits.  This module exposes exact ground
theorems for those projections and gives small canonical models for each one.
-/

namespace GaloisForLFunctions

noncomputable section

namespace UniformBoundaryWedge

/-- The left vertex of a two-vertex wedge lies in the opposite left facet. -/
theorem boundaryWedgeLeftFacetMember_witness :
    boundaryWedgeLeftFacetMember (r := 1) (s := 1) none
      (some (Sum.inl 0)) := by
  simp [boundaryWedgeLeftFacetMember, boundaryWedgeLeft,
    boundaryWedgeLeftVertex]

/-- The right vertex of a two-vertex wedge lies in the opposite right facet. -/
theorem boundaryWedgeRightFacetMember_witness :
    boundaryWedgeRightFacetMember (r := 1) (s := 1) none
      (some (Sum.inr 0)) := by
  simp [boundaryWedgeRightFacetMember, boundaryWedgeRight,
    boundaryWedgeRightVertex]

end UniformBoundaryWedge

namespace HTGeometry

/-- Constraint geometry in which every finite set is a face. -/
def universalConstraintGeometry (α : Type*) [DecidableEq α] :
    AbstractConstraintGeometry α where
  IsFace := fun _ => True
  downward := fun _ _ => trivial

/-- Every finite set is a face of the universal constraint geometry. -/
theorem universalConstraintGeometry_isFace
    {α : Type*} [DecidableEq α] (J : Finset α) :
    (universalConstraintGeometry α).IsFace J :=
  trivial

/-- Canonical orientation thread whose faces are exactly supported finite subsets. -/
def supportedConstraintOrientationThread
    (α β : Type*) [DecidableEq α] [DecidableEq β] :
    FiniteConstraintOrientationThread α β where
  face := fun S J => J ⊆ S
  face_supported := fun h => h
  face_downward := fun hIJ hJS => hIJ.trans hJS
  negative := fun _ => ∅
  negative_supported := fun _ => Finset.empty_subset _
  face_compatible := by
    intro S T hST J hJS
    constructor
    · exact fun _ => hJS.trans hST
    · exact fun _ => hJS
  negative_compatible := by simp

/-- Every supported finite subset is a face in the canonical orientation thread. -/
theorem supportedConstraintOrientationThread_face
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S J : Finset α} (hJS : J ⊆ S) :
    (supportedConstraintOrientationThread α β).face S J :=
  hJS

/-- Total admission with the unique unit observation. -/
def totalUnitPartialCompletion (X : Type*) : PartialCompletion X Unit where
  admissible := fun _ => True
  observe := fun _ => ()

/-- Every source point is admitted by total unit completion. -/
theorem totalUnitPartialCompletion_admissible
    {X : Type*} (x : X) :
    (totalUnitPartialCompletion X).admissible x :=
  trivial

namespace DerivedSelection

/-- Zero matrix is a relation matrix for every finite generating family. -/
theorem isRelMatrix_zero
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) :
    IsRelMatrix π 0 := by
  intro j
  change π 0 = 0
  exact map_zero π

end DerivedSelection

end HTGeometry

end

end GaloisForLFunctions
