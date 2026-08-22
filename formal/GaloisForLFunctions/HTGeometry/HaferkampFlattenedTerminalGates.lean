import GaloisForLFunctions.HTGeometry.HaferkampBlockFlattening

/-!
# Literal terminal gates of a flattened BLC assembly

The recursive assembly retains an actual local `SU(4)` terminal gate for each
selected coordinate.  This module exposes those gates in the same finite order
as the requested Pauli labels and proves that their total lifts are exactly the
entries of the flattened physical word.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- Local terminal `SU(4)` gates in requested-label order. -/
def TerminalBlockPrefixAssembly.terminalLocalGates
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
  | .nil _ => []
  | .cons step tail => step.block.terminalGate :: tail.terminalLocalGates

/-- The terminal-local-gate list has one entry for each requested label. -/
theorem TerminalBlockPrefixAssembly.terminalLocalGates_length_eq_labels_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.terminalLocalGates.length = labels.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih => simp [terminalLocalGates, ih]

/-- The actual local `SU(4)` gate associated with one retained terminal
coordinate. -/
def TerminalBlockPrefixAssembly.terminalLocalGate
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) : Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  assembly.terminalLocalGates.get ⟨i.1, by
    rw [assembly.terminalLocalGates_length_eq_labels_length]
    exact i.2⟩

/-- The first retained local gate is the current block's terminal gate. -/
theorem TerminalBlockPrefixAssembly.terminalLocalGate_cons_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps) :
    (TerminalBlockPrefixAssembly.cons step tail).terminalLocalGate 0 =
      step.block.terminalGate := rfl

/-- Every later retained local gate is the corresponding tail gate. -/
theorem TerminalBlockPrefixAssembly.terminalLocalGate_cons_succ
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps)
    (i : Fin Ps.length) :
    (TerminalBlockPrefixAssembly.cons step tail).terminalLocalGate (Fin.succ i) =
      tail.terminalLocalGate i := rfl

/-- Flattened terminal positions evaluate to the lifted versions of their
retained local `SU(4)` gates. -/
theorem TerminalBlockPrefixAssembly.liftedWord_get_terminalLocalGate
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    assembly.liftedWord.get (assembly.terminalIndices i) =
      totalTwoQubitLift (cone.mergePlan.terminal, root) (assembly.terminalLocalGate i) := by
  induction assembly with
  | nil => exact Fin.elim0 i
  | @cons pre P Ps step tail ih =>
      refine Fin.cases ?_ ?_ i
      · rw [TerminalBlockPrefixAssembly.terminalGate_cons_zero step tail,
          TerminalBlockPrefixAssembly.terminalLocalGate_cons_zero step tail]
      · intro j
        rw [TerminalBlockPrefixAssembly.terminalGate_cons_succ step tail j,
          TerminalBlockPrefixAssembly.terminalLocalGate_cons_succ step tail j]
        exact ih j

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
