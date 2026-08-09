import GaloisForLFunctions.HTGeometry.TwoReplicaNonzeroPauliInternalReproduction
import GaloisForLFunctions.HTGeometry.LinearFamilyGreatestMaximizer

/-!
# Internal reproduction at the canonical obstruction

The greatest defect maximizer of a linear-map family is a function of the family, so the
internal-reproduction theorem needs no hypothesis: stating it at the canonical obstruction of the
weight-at-most-`q` two-replica collective Pauli family discharges the greatest-maximizer condition
outright.

The resolved nonzero paired-Pauli character sector of that obstruction is reproduced by literal
weight-one collective Pauli commutators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The canonical greatest maximum-defect subspace of the weight-at-most-`q` two-replica collective
Pauli family. -/
def canonicalTwoReplicaQLocalObstruction (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Submodule ℂ (FiniteTwoReplicaMatrix V) :=
  linearFamilyGreatestMaximizer (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)

omit [LinearOrder V] in
theorem le_canonicalTwoReplicaQLocalObstruction (q : ℕ)
    (W : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (h : linearFamilyDefect (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W
      = linearFamilyDefect (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
          (canonicalTwoReplicaQLocalObstruction V q)) :
    W ≤ canonicalTwoReplicaQLocalObstruction V q :=
  le_linearFamilyGreatestMaximizer _ W h

/-- **The nonzero-character sector reproduces itself, unconditionally.**  The complete resolved
nonzero paired-Pauli character sector of the canonical weight-at-most-`q` obstruction lies inside
its own one-step shadow under the literal weight-one collective Pauli family. -/
theorem finiteTwoReplicaNonzeroPauliResolvedSubspace_canonical_le_shadow (q : ℕ) :
    finiteTwoReplicaNonzeroPauliResolvedSubspace (canonicalTwoReplicaQLocalObstruction V q) ≤
      linearFamilyShadow (finiteTwoReplicaQLocalCollectiveCommutatorLinear V 1)
        (finiteTwoReplicaNonzeroPauliResolvedSubspace
          (canonicalTwoReplicaQLocalObstruction V q)) :=
  finiteTwoReplicaNonzeroPauliResolvedSubspace_le_shadow_of_greatestMaximizer q
    (canonicalTwoReplicaQLocalObstruction V q)
    (fun W hW => le_canonicalTwoReplicaQLocalObstruction q W hW)

end

end GaloisForLFunctions.HTGeometry
