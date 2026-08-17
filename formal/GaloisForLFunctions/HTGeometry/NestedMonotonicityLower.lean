import GaloisForLFunctions.HTGeometry.NestedMonotonicityPhaseTail

/-!
# Early-time lower bound for the literal-monotonicity counterexample
-/

open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- Any circuit approximating the early-time nested evolution uses more than `1513` two-qubit
gates. -/
theorem monotonicityCounterEarly_twoGateCount_gt
    (c : List (LocalGate (PairQubit monotonicityCounterLength)))
    (hclose : ‖circuitMatrix c - nestedInversePowerChainEvolution
      monotonicityCounterLength monotonicityCounterEarlyTime‖ ≤
        monotonicityCounterEpsilon) :
    monotonicityCounterGateBudget < twoGateCount c := by
  have hL : 0 < monotonicityCounterLength := by
    norm_num [monotonicityCounterLength]
  have hsdelta : monotonicityCounterEarlyTime + monotonicityCounterDelta =
      2 * Real.pi := by
    unfold monotonicityCounterEarlyTime
    ring
  refine treePhase_twoGateCount_gt
    (nestedQubitPathGraph monotonicityCounterLength)
    (nestedQubitPathGraph_isTree hL)
    (nestedFoldedPhase monotonicityCounterLength monotonicityCounterEarlyTime
      monotonicityCounterDelta) c (ε := monotonicityCounterEpsilon) ?_ ?_
  · rw [nestedFoldedPhaseEvolution_eq hL hsdelta]
    exact hclose
  · intro N hN hcard
    unfold monotonicityCounterLength at hN ⊢
    unfold monotonicityCounterGateBudget at hcard
    exact counterEveryDeletion_chord N hN hcard

/-- Integer-valued early complexity is at least `1514`. -/
theorem monotonicityCounterEarly_complexity_lower :
    (1514 : ℕ∞) ≤ nestedOperatorTwoGateComplexity
      monotonicityCounterLength monotonicityCounterEpsilon
      monotonicityCounterEarlyTime := by
  rw [le_nestedOperatorTwoGateComplexity_iff]
  intro c hc
  have hgt := monotonicityCounterEarly_twoGateCount_gt c hc
  norm_num [monotonicityCounterGateBudget] at hgt ⊢
  exact_mod_cast (by omega : 1514 ≤ twoGateCount c)

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
