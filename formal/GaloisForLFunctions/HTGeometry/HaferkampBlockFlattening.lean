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

/-- The element immediately after a list prefix is the head of the remaining
suffix.  Stating this independently of a dependent record avoids index
transport when selecting terminal gates. -/
theorem list_get_terminal_of_decomp
    {α : Type*} (before after : List α) (terminal : α)
    (gates : List α) (hdecomp : gates = before ++ terminal :: after) :
    gates.get ⟨before.length, by rw [hdecomp]; simp⟩ = terminal := by
  subst gates
  simp

/-- The prefix preceding a bundled terminal gate is literally the corresponding
`take` of its lifted physical gate word. -/
theorem TerminalBlockData.take_liftedWord_prefix
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) :
    List.take block.prefixGates.length
      (List.zipWith totalTwoQubitLift edges block.gates) =
      List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates := by
  rcases block with ⟨gates, terminalGate, prefixEdges, suffixEdges, prefixGates, suffixGates,
    gatesLength, gatesClifford, edgesDecomp, gatesDecomp, prefixLength, suffixLength,
    suffixIdentity, transportCoeff, transportCoeffNonzero, transport, curveLength, curveZero,
    contractionDerivative⟩
  simp only
  rw [edgesDecomp, gatesDecomp, List.zipWith_append prefixLength.symm]
  have hlength : prefixGates.length =
      (List.zipWith totalTwoQubitLift prefixEdges prefixGates).length := by
    rw [List.length_zipWith]
    symm
    exact Nat.min_eq_right (Nat.le_of_eq prefixLength)
  have hle : prefixGates.length ≤
      (List.zipWith totalTwoQubitLift prefixEdges prefixGates).length := by
    rw [← hlength]
  rw [List.take_append_of_le_length hle, hlength,
    List.take_length]

/-- The lifted word of a bundled block decomposes at its retained terminal
gate, with the terminal interpreted at the root-targeting edge. -/
theorem TerminalBlockData.liftedWord_decomp_at
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) (terminalEdge : Fin n × Fin n)
    (hedges : edges = block.prefixEdges ++ terminalEdge :: block.suffixEdges) :
    List.zipWith totalTwoQubitLift edges block.gates =
      List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates ++
        totalTwoQubitLift terminalEdge block.terminalGate ::
          List.zipWith totalTwoQubitLift block.suffixEdges block.suffixGates := by
  rcases block with ⟨gates, terminalGate, prefixEdges, suffixEdges, prefixGates, suffixGates,
    gatesLength, gatesClifford, edgesDecomp, gatesDecomp, prefixLength, suffixLength,
    suffixIdentity, transportCoeff, transportCoeffNonzero, transport, curveLength, curveZero,
    contractionDerivative⟩
  simp only
  change edges = prefixEdges ++ terminalEdge :: suffixEdges at hedges
  rw [hedges, gatesDecomp, List.zipWith_append prefixLength.symm]
  rfl

/-- The retained terminal coordinate is a valid local gate index. -/
theorem TerminalBlockData.prefixGates_length_lt_gates_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) :
    block.prefixGates.length < block.gates.length := by
  rcases block with ⟨gates, terminalGate, prefixEdges, suffixEdges, prefixGates, suffixGates,
    gatesLength, gatesClifford, edgesDecomp, gatesDecomp, prefixLength, suffixLength,
    suffixIdentity, transportCoeff, transportCoeffNonzero, transport, curveLength, curveZero,
    contractionDerivative⟩
  simp only
  rw [gatesDecomp, List.length_append, List.length_cons]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

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
  | nil => simp [liftedWord, finalPrefix]
  | cons step tail ih =>
      simp only [liftedWord, finalPrefix, List.reverse_append, List.prod_append]
      rw [mul_assoc]
      change tail.liftedWord.reverse.prod *
        (edgeListBlockContraction edges step.block.gates * _) = tail.finalPrefix
      exact ih

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
