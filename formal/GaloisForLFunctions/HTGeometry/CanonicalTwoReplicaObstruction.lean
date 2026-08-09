import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalPauliHallSymmetryReduction
import GaloisForLFunctions.HTGeometry.LinearFamilyGreatestMaximizer

/-!
# The canonical two-replica Hall obstruction

The greatest defect maximizer of a linear-map family is a function of the family, so the
weight-at-most-`q` two-replica collective Pauli family has one canonical obstruction rather than a
class of subspaces meeting a condition.

Naming it turns every statement of the form "let `U` be the greatest maximizer, then …" into a
statement about a single subspace, with the condition discharged.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical greatest maximum-defect subspace of the weight-at-most-`q` two-replica collective
Pauli family. -/
def canonicalTwoReplicaQLocalObstruction (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Submodule ℂ (FiniteTwoReplicaMatrix V) :=
  linearFamilyGreatestMaximizer (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)

/-- **The canonical obstruction is greatest.**  This discharges the greatest-maximizer premise of
every conditional two-replica statement. -/
theorem le_canonicalTwoReplicaQLocalObstruction (q : ℕ)
    (W : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (h : linearFamilyDefect (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W
      = linearFamilyDefect (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
          (canonicalTwoReplicaQLocalObstruction V q)) :
    W ≤ canonicalTwoReplicaQLocalObstruction V q :=
  le_linearFamilyGreatestMaximizer _ W h

/-- The canonical obstruction maximizes the deficiency. -/
theorem linearFamilyDefect_le_canonicalTwoReplicaQLocalObstruction (q : ℕ)
    (W : Submodule ℂ (FiniteTwoReplicaMatrix V)) :
    linearFamilyDefect (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W
      ≤ linearFamilyDefect (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
          (canonicalTwoReplicaQLocalObstruction V q) :=
  linearFamilyDefect_le_greatestMaximizer _ W

end

end GaloisForLFunctions.HTGeometry
