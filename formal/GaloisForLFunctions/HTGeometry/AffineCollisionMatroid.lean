import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# The collision matroid of a frame map

A family indexed by `Λ` whose only dependencies come from repeated values of a frame map
`frame : Λ → Frame` represents the pullback of the free matroid on `Frame`.  Thus its independent
sets are exactly the sets on which `frame` is injective, and its rank is the number of distinct
frames.  This is the precise partition-matroid object used by affine jet-packet collision laws.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- The collision matroid represented by a frame map: two indices are parallel exactly when they
have the same frame. -/
def affineCollisionMatroid {Λ Frame : Type*} (frame : Λ → Frame) : Matroid Λ :=
  (Matroid.freeOn Set.univ).comap frame

@[simp]
theorem affineCollisionMatroid_ground {Λ Frame : Type*} (frame : Λ → Frame) :
    (affineCollisionMatroid frame).E = Set.univ := by
  simp [affineCollisionMatroid]

/-- Independence in the collision matroid is injectivity of the frame map. -/
theorem affineCollisionMatroid_indep_iff {Λ Frame : Type*}
    (frame : Λ → Frame) (I : Set Λ) :
    (affineCollisionMatroid frame).Indep I ↔ Set.InjOn frame I := by
  simp [affineCollisionMatroid]

/-- The extended rank of any index set is the cardinality of its set of distinct frames. -/
theorem affineCollisionMatroid_eRk {Λ Frame : Type*}
    (frame : Λ → Frame) (I : Set Λ) :
    (affineCollisionMatroid frame).eRk I = (frame '' I).encard := by
  rw [affineCollisionMatroid, Matroid.eRk_comap,
    Matroid.eRk_freeOn (Set.subset_univ (frame '' I))]

/-- On a finite packet, collision-matroid rank is the number of distinct frames. -/
theorem affineCollisionMatroid_eRk_finset {Λ Frame : Type*} [DecidableEq Frame]
    (frame : Λ → Frame) (E : Finset Λ) :
    (affineCollisionMatroid frame).eRk (↑E : Set Λ) = (E.image frame).card := by
  rw [affineCollisionMatroid_eRk]
  calc
    (frame '' (↑E : Set Λ)).encard = (↑(E.image frame) : Set Frame).encard := by
      congr 1
      ext x
      simp
    _ = (E.image frame).card := Set.encard_coe_eq_coe_finsetCard _

end GaloisForLFunctions.HTGeometry
