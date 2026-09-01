import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.NestedPathCutWitness

/-!
# Finite target profiles for nested qubit paths

Closed finite-volume isoperimetric applications of arXiv:2603.03257 to physical qubit paths.
-/

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- Every physical two-state qubit cell has positive target-avoiding profile between its two
Boolean vertices. -/
theorem nestedQubitPathGraph_pair_targetAvoidingIsoperimetricProfile_pos
    {L : ℕ} (j : Fin L) :
    0 < GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile
      (nestedQubitPathGraph L)
      ({(j, false)} : Finset (PairQubit L)) ({(j, true)} : Finset (PairQubit L)) := by
  apply GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile_pos_of_adj
  exact nestedQubitPathGraph_adj_pair j

/-- Every bridge between consecutive qubit cells has positive target-avoiding profile. -/
theorem nestedQubitPathGraph_bridge_targetAvoidingIsoperimetricProfile_pos
    {L : ℕ} (j : Fin (L - 1)) :
    0 < GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile
      (nestedQubitPathGraph L)
      ({(nestedBridgeLeft j, true)} : Finset (PairQubit L))
      ({(nestedBridgeRight j, false)} : Finset (PairQubit L)) := by
  apply GaloisForLFunctions.HTGeometry.targetAvoidingIsoperimetricProfile_pos_of_adj
  exact nestedQubitPathGraph_adj_bridge j

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
