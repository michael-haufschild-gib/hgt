import GaloisForLFunctions.HTGeometry.TwoReplicaFirstOrderCliffordInterpolation
import GaloisForLFunctions.HTGeometry.CanonicalTwoReplicaObstruction

/-!
# First-order interpolation at the canonical obstruction

First-order Clifford interpolation writes a one-site collective commutator on an odd paired-Pauli
direction as a difference of two product-Clifford conjugates.  A product-Clifford invariant subspace
therefore contains that commutator image outright — no square, and no differentiation of a finite
group action.

Stated at the canonical obstruction of the weight-at-most-`q` family, the invariance premise is
discharged and the containment is unconditional.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **One-site commutator images of odd directions stay inside the canonical obstruction.** -/
theorem finiteTwoReplicaSingleSiteCollectiveCommutator_mem_canonicalObstruction_of_relativeOdd
    (q : ℕ) (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V)
    (hX : X ∈ canonicalTwoReplicaQLocalObstruction V q)
    (hodd : finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) * X *
        finiteTwoReplicaPairedPauli (finiteSingleSitePauliLabel j a) = -X) :
    finiteTwoReplicaCollectiveCommutatorLinear (finiteSingleSitePauliLabel j a) X
      ∈ canonicalTwoReplicaQLocalObstruction V q :=
  finiteTwoReplicaSingleSiteCollectiveCommutator_mem_greatestMaximizer_of_relativeOdd q
    (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW) j a X hX hodd

/-- **First-defect selected images stay inside the canonical obstruction.** -/
theorem firstDefectCollectiveCommutator_mem_canonicalObstruction [LinearOrder V]
    (q : ℕ) (P : NonzeroPauliCharacter V) (X : FiniteTwoReplicaMatrix V)
    (hXU : X ∈ canonicalTwoReplicaQLocalObstruction V q)
    (hXP : X ∈ finiteTwoReplicaPauliCharacterSubspace P.1) :
    finiteTwoReplicaCollectiveCommutatorLinear (firstDefectPauliLabel P) X
      ∈ canonicalTwoReplicaQLocalObstruction V q :=
  firstDefectCollectiveCommutator_mem_greatestMaximizer q
    (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW) P X hXU hXP

end

end GaloisForLFunctions.HTGeometry
