import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapScalarNormalizer

/-! # Retain the equality certificate produced during scalar normalization -/
namespace HTGeometry

/-- A normalized scalar accompanied by its exact source equality. -/
structure CompactGapNormalForm (source : ℝ) where
  value : ℝ
  eq_value : source = value

open Lean Meta Elab Term Tactic
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

meta section
elab "compactGapCertified% " cnv:conv " => " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Real))
  let (rhs, g) ← Conv.mkConvGoalFor e
  let goals ← Tactic.run g.mvarId! do
    evalTactic cnv
    for goal in (← getGoals) do
      goal.refl
    pruneSolvedGoals
  unless goals.isEmpty do
    throwError "certified normalization left open goals"
  let rhs ← instantiateMVars rhs
  let proof ← instantiateMVars g
  return mkApp3 (mkConst ``CompactGapNormalForm.mk) e rhs proof
end

end HTGeometry
