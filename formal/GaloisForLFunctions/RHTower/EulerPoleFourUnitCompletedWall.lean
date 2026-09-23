import GaloisForLFunctions.RHTower.EulerPoleBoundaryBudget
import GaloisForLFunctions.RHTower.SuzukiCauchyWallHardyEvaluation

/-!
# Exact Euler-pole budget for the completed Suzuki source wall

This leaf identifies the fixed four-unit incoming Euler-pole norm with the literal completed
prime--polar wall bound.  It does not assume or construct the still-open cofinal `L²` transport:
the nonexpansive source-wall statement itself is proved exactly equivalent to RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every finite completed Suzuki source wall stays below the incoming Euler-pole `L²` budget. -/
def EulerPoleCompletedWallNonexpansive : Prop :=
  ∀ N : ℕ,
    ‖GaloisForLFunctions.RHTower.suzukiUnitRieszCompletedCauchyWallSymbolComplex
      (N + 2) (-I)‖ ^ (2 : ℕ) ≤ ‖eulerPoleBoundaryProfileL2‖ ^ (2 : ℕ)

/-- The literal completed wall is nonexpansive against the Euler-pole profile exactly under RH. -/
theorem eulerPoleCompletedWallNonexpansive_iff_riemannHypothesis :
    EulerPoleCompletedWallNonexpansive ↔ RiemannHypothesis := by
  rw [EulerPoleCompletedWallNonexpansive, norm_eulerPoleBoundaryProfileL2_sq]
  exact GaloisForLFunctions.RHTower.riemannHypothesis_iff_suzukiCompletedCauchyWall_neg_I_sq_le_four.symm

/-- Off RH, some literal completed source wall strictly exceeds the incoming pole budget. -/
theorem exists_completedWall_gt_eulerPoleBoundaryBudget_iff_not_riemannHypothesis :
    (∃ N : ℕ,
      ‖eulerPoleBoundaryProfileL2‖ ^ (2 : ℕ) <
        ‖GaloisForLFunctions.RHTower.suzukiUnitRieszCompletedCauchyWallSymbolComplex
          (N + 2) (-I)‖ ^ (2 : ℕ)) ↔ ¬ RiemannHypothesis := by
  rw [← not_congr eulerPoleCompletedWallNonexpansive_iff_riemannHypothesis]
  simp only [EulerPoleCompletedWallNonexpansive, not_forall, not_le]

/-- Closed headline package: incoming norm is exactly four and its completed-wall
nonexpansiveness is exactly RH. -/
theorem eulerPoleFourUnitCompletedWallLaw :
    ‖eulerPoleBoundaryProfileL2‖ ^ (2 : ℕ) = 4 ∧
      (EulerPoleCompletedWallNonexpansive ↔ RiemannHypothesis) :=
  ⟨norm_eulerPoleBoundaryProfileL2_sq,
    eulerPoleCompletedWallNonexpansive_iff_riemannHypothesis⟩

end

end RHTower
