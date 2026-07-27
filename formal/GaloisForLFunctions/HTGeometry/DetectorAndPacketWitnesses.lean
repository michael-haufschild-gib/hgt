import GaloisForLFunctions.HTGeometry.LinearWidthThreeStepDetector
import GaloisForLFunctions.HTGeometry.QuadraticQuantumDetectorRepresentation
import GaloisForLFunctions.HTGeometry.AffineJetPacketCollisionCompletion
import GaloisForLFunctions.HTGeometry.QuasiAbelianFacetPaletteCompletion

/-!
# Inhabitants of the detector indices and packet inputs

Four more bundles that are consumed as hypotheses and constructed nowhere.

The two detector indices are inductive types with a nullary grade — the membrane point and the
vacuum root — so they are inhabited for every rank; the instances record it.

The collision input is realized with empty defect sets: there is nothing to avoid, so every source
has the generic orbit rank and satisfies the operator rank law.  The facet-palette input is realized
on the empty facet family, where both of its fields quantify over an empty index; this is the
degenerate end of the palette, and it shows the bundle is consistent.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ### Detector indices -/

/-- The membrane point inhabits the linear-width detector index in every rank. -/
instance nonempty_linearWidthDetectorIndex (n : ℕ) : Nonempty (LinearWidthDetectorIndex n) :=
  ⟨LinearWidthDetectorIndex.membrane⟩

/-- The vacuum root inhabits the quadratic detector index in every rank. -/
instance nonempty_quadraticQuantumDetectorIndex (n : ℕ) :
    Nonempty (QuadraticQuantumDetectorIndex n) :=
  ⟨QuadraticQuantumDetectorIndex.root⟩

/-! ### The affine jet packet collision input -/

/-- **A collision input with empty defect.**  Nothing is excluded, so every source avoids all defect
sets and therefore has the generic orbit rank `|frame(E)|` and satisfies the operator rank law. -/
def affineJetPacketCollisionInput_empty {X Λ Frame : Type*} [TopologicalSpace X]
    [DecidableEq Frame] (frame : Λ → Frame) :
    AffineJetPacketCollisionInput X Λ Frame frame where
  defect := fun _ => (∅ : Set X)
  orbitRank := fun _ E => (E.image frame).card
  operatorRankLaw := fun _ => True
  defect_closed := fun _ => isClosed_empty
  defect_interior_empty := fun _ => interior_empty
  collisionRank_of_avoids := fun _ _ _ => rfl
  operatorRank_of_avoids := fun _ _ => trivial

/-! ### The quasi-Abelian facet palette input -/

/-- **The palette input on the empty facet family.**  Both fields quantify over the facets, so on the
empty family they hold vacuously; the bundle is therefore consistent. -/
def quasiAbelianFacetPaletteInput_empty {α : Type*} [Fintype α] [DecidableEq α] (omega : α → ℝ) :
    QuasiAbelianFacetPaletteInput α (∅ : Finset (Finset α)) omega where
  certificate := fun F => absurd F.2 (Finset.notMem_empty _)
  latticeClass_eq_implies_shift_eq := fun F => absurd F.2 (Finset.notMem_empty _)

end GaloisForLFunctions.HTGeometry
