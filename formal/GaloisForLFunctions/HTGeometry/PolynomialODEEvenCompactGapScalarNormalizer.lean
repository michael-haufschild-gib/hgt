import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSliceNormalizer
import Mathlib.Tactic.DSimpPercent

/-! # Scalar normal-form syntax for independently checked cofactor identities -/
namespace HTGeometry
open Lean Meta Elab Term Tactic
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

meta section
elab "compactGapNormalize% " cnv:conv " => " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Real))
  let (rhs, g) ← Conv.mkConvGoalFor e
  let goals ← Tactic.run g.mvarId! do
    evalTactic cnv
    for goal in (← getGoals) do
      goal.refl
    pruneSolvedGoals
  unless goals.isEmpty do
    throwError "scalar normalization left open goals"
  instantiateMVars rhs
end

end HTGeometry
