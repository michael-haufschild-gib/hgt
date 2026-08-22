import GaloisForLFunctions.HTGeometry.HaferkampTerminalSignControl
import GaloisForLFunctions.HTGeometry.HaferkampBlockFlattening

/-!
# Sign control in flattened terminal coordinates

Every scalar retained by the recursive terminal-coordinate flattening is the
inverse product of two Pauli--Clifford signs, hence a sign itself.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- Every flattened terminal coordinate has a real sign coefficient. -/
theorem TerminalBlockPrefixAssembly.terminalCoefficient_eq_one_or_neg_one
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    assembly.terminalCoefficient i = 1 ∨ assembly.terminalCoefficient i = -1 := by
  induction assembly with
  | nil => exact Fin.elim0 i
  | @cons pre P Ps step tail ih =>
      refine Fin.cases ?_ ?_ i
      · rw [TerminalBlockPrefixAssembly.terminalCoefficient_cons_zero]
        exact step.strippedCoeff_eq_one_or_neg_one
      · intro j
        rw [TerminalBlockPrefixAssembly.terminalCoefficient_cons_succ]
        exact ih j

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
