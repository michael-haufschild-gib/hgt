import GaloisForLFunctions.HTGeometry.HaferkampBlockPrefixAssembly

/-!
# Flattening terminal-aware BLC block assemblies

The recursive assembly stores one physical word per BLC block.  These
definitions flatten it to the single chronological word used by the circuit
contraction and retain the selected terminal offsets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

/-- The literal chronological local-gate word of a recursive BLC assembly. -/
def TerminalBlockPrefixAssembly.gateWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
  | .nil _ => []
  | .cons step tail => step.block.gates ++ tail.gateWord

/-- The corresponding flattened word of full-register lifted unitaries. -/
def TerminalBlockPrefixAssembly.liftedWord
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      List (Matrix.unitaryGroup (Fin n → Bool) ℂ)
  | .nil _ => []
  | .cons step tail =>
      List.zipWith totalTwoQubitLift edges step.block.gates ++ tail.liftedWord

/-- Offsets of the terminal coordinates in the flattened chronological word. -/
def TerminalBlockPrefixAssembly.terminalOffsets
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels → List ℕ
  | .nil _ => []
  | .cons step tail =>
      step.block.prefixGates.length ::
        (tail.terminalOffsets.map (step.block.gates.length + ·))

/-- The unitary obtained after executing every block in an assembly. -/
def TerminalBlockPrefixAssembly.finalPrefix
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels →
      Matrix.unitaryGroup (Fin n → Bool) ℂ
  | .nil pre => pre
  | .cons _ tail => tail.finalPrefix

/-- Flattening preserves the number of chronological local gates. -/
theorem TerminalBlockPrefixAssembly.liftedWord_length_eq_gateWord_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.liftedWord.length = assembly.gateWord.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      simp [liftedWord, gateWord, step.block.gates_length, ih]

/-- There is exactly one retained terminal offset per recursively assembled
block, hence one per requested Pauli label. -/
theorem TerminalBlockPrefixAssembly.terminalOffsets_length_eq_labels_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.terminalOffsets.length = labels.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih => simp [terminalOffsets, ih]

/-- The reverse product of the flattened lifted word composes exactly with
its incoming prefix to the final recursively indexed prefix. -/
theorem TerminalBlockPrefixAssembly.reverse_prod_mul_eq_finalPrefix
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.liftedWord.reverse.prod * pre = assembly.finalPrefix := by
  induction assembly with
  | nil => rfl
  | cons step tail ih =>
      change (tail.liftedWord.reverse.prod *
        (List.zipWith totalTwoQubitLift edges step.block.gates).reverse.prod) * _ = _
      rw [← mul_assoc]
      change tail.liftedWord.reverse.prod *
        (edgeListBlockContraction edges step.block.gates * _) = tail.finalPrefix
      exact ih

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
