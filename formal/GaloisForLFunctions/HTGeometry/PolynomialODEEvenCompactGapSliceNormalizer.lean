import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSourceCoefficients

/-! # Normalized source-coefficient syntax with independent coefficient proofs -/
namespace HTGeometry
open Lean Meta Elab Term Tactic
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

meta section
elab "compactGapSlice% " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Real))
  let (rhs, g) ← Conv.mkConvGoalFor e
  let goals ← Tactic.run g.mvarId! do
    evalTactic (← `(conv| norm_num [evenCompactGapSourceZeroCoeff,
      evenCompactGapReflectedTwoCoeff, evenCompactGapReflectedFourCoeff,
      evenCompactGapReflectedSixCoeff, evenCompactGapReflectedEightCoeff,
      evenCompactGapReflectedTenCoeff, evenCompactGapReflectedTwelveCoeff]))
    for goal in (← getGoals) do
      goal.refl
    pruneSolvedGoals
  unless goals.isEmpty do
    throwError "source coefficient normalization left open goals"
  instantiateMVars rhs
end

end HTGeometry
