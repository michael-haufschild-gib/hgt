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

/-- The position immediately after a prefix is a valid index of a list with a
terminal element following that prefix. -/
theorem list_before_length_lt_of_decomp
    {α : Type*} (before after : List α) (terminal : α)
    (gates : List α) (hdecomp : gates = before ++ terminal :: after) :
    before.length < gates.length := by
  subst gates
  rw [List.length_append, List.length_cons]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

/-- A suffix of local identity gates contributes identity to the reverse
physical product, even when its edge list is only aligned by `zipWith`. -/
theorem suffix_lifted_reverse_prod_eq_one
    {n : ℕ} (edges : List (Fin n × Fin n))
    (gates : List (Matrix.specialUnitaryGroup (Bool × Bool) ℂ))
    (hidentity : ∀ U ∈ gates, U = 1) :
    (List.zipWith totalTwoQubitLift edges gates).reverse.prod = 1 := by
  induction edges generalizing gates with
  | nil => simp
  | cons edge edges ih =>
      cases gates with
      | nil => simp
      | cons gate gates =>
          rw [List.zipWith, List.reverse_cons, List.prod_append,
            List.prod_cons, List.prod_nil, hidentity gate (by simp),
            totalTwoQubitLift_one, mul_one]
          rw [mul_one]
          apply ih gates
          intro U hU
          exact hidentity U (List.mem_cons_of_mem _ hU)

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

/-- After removing the identity suffix, a terminal-aware block contraction is
the selected terminal lift followed by its literal preceding physical word. -/
theorem TerminalBlockData.contraction_eq_terminal_mul_prefix
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) :
    edgeListBlockContraction edges block.gates =
      totalTwoQubitLift (cone.mergePlan.terminal, root) block.terminalGate *
        (List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates).reverse.prod := by
  rcases block with ⟨gates, terminalGate, prefixEdges, suffixEdges, prefixGates, suffixGates,
    gatesLength, gatesClifford, edgesDecomp, gatesDecomp, prefixLength, suffixLength,
    suffixIdentity, transportCoeff, transportCoeffNonzero, transport, curveLength, curveZero,
    contractionDerivative⟩
  change haferkampGateWordReverseProduct totalTwoQubitLift edges gates = _
  rw [edgesDecomp, gatesDecomp,
    haferkampGateWordReverseProduct_append totalTwoQubitLift prefixEdges
      ((cone.mergePlan.terminal, root) :: suffixEdges) prefixGates
      (terminalGate :: suffixGates) prefixLength,
    haferkampGateWordReverseProduct_cons]
  rw [suffix_lifted_reverse_prod_eq_one suffixEdges suffixGates suffixIdentity]
  simp

/-- The terminal Pauli conjugation written at the local coordinate is exactly
the corresponding conjugation by the whole block contraction. -/
theorem TerminalBlockData.local_conjugation_eq_block_conjugation
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P)
    (Z : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Matrix.conjTranspose
        (((List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates).reverse.prod :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      Matrix.conjTranspose
        (totalTwoQubitLift (cone.mergePlan.terminal, root) block.terminalGate :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        Z *
        (totalTwoQubitLift (cone.mergePlan.terminal, root) block.terminalGate :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (((List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates).reverse.prod :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      Matrix.conjTranspose (edgeListBlockContraction edges block.gates :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * Z *
        (edgeListBlockContraction edges block.gates :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  rw [block.contraction_eq_terminal_mul_prefix]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The retained local index evaluates to the lifted terminal gate at the
root-targeting edge. -/
theorem TerminalBlockData.liftedWord_get_terminal
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root} {P : Fin n → Option (Fin 3)}
    (block : TerminalBlockData cone P) :
    (List.zipWith totalTwoQubitLift edges block.gates).get
      ⟨block.prefixGates.length, by
        have hfull : (List.zipWith totalTwoQubitLift edges block.gates).length =
            block.gates.length := by
          rw [List.length_zipWith]
          simp [block.gates_length]
        rw [hfull]
        exact block.prefixGates_length_lt_gates_length⟩ =
      totalTwoQubitLift (cone.mergePlan.terminal, root) block.terminalGate := by
  have hpref :
      (List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates).length =
        block.prefixGates.length := by
    rw [List.length_zipWith]
    exact Nat.min_eq_right (Nat.le_of_eq block.prefix_length)
  have hdecomp := block.liftedWord_decomp_at
    (cone.mergePlan.terminal, root) block.edges_decomp
  have hget := list_get_terminal_of_decomp
    (List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates)
    (List.zipWith totalTwoQubitLift block.suffixEdges block.suffixGates)
    (totalTwoQubitLift (cone.mergePlan.terminal, root) block.terminalGate)
    (List.zipWith totalTwoQubitLift edges block.gates) hdecomp
  simpa [hpref] using hget

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

/-- Every retained terminal offset is a valid coordinate of the flattened
physical word. -/
theorem TerminalBlockPrefixAssembly.terminalOffset_lt_liftedWord_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) {offset : ℕ}
    (hmem : offset ∈ assembly.terminalOffsets) :
    offset < assembly.liftedWord.length := by
  induction assembly generalizing offset with
  | nil => simp [TerminalBlockPrefixAssembly.terminalOffsets] at hmem
  | cons step tail ih =>
      simp only [TerminalBlockPrefixAssembly.terminalOffsets, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst offset
        have hlocal := step.block.prefixGates_length_lt_gates_length
        have hlifted :
            (List.zipWith totalTwoQubitLift edges step.block.gates).length =
              step.block.gates.length := by
          rw [List.length_zipWith]
          simp [step.block.gates_length]
        simp only [TerminalBlockPrefixAssembly.liftedWord, List.length_append]
        change step.block.prefixGates.length <
          (List.zipWith totalTwoQubitLift edges step.block.gates).length +
            tail.liftedWord.length
        exact lt_of_lt_of_le (by simpa [hlifted] using hlocal) (Nat.le_add_right _ _)
      · obtain ⟨offset, hmem, rfl⟩ := List.mem_map.mp htail
        have htail_lt := ih hmem
        have hlifted :
            (List.zipWith totalTwoQubitLift edges step.block.gates).length =
              step.block.gates.length := by
          rw [List.length_zipWith]
          simp [step.block.gates_length]
        simp only [TerminalBlockPrefixAssembly.liftedWord, List.length_append]
        change step.block.gates.length + offset <
          (List.zipWith totalTwoQubitLift edges step.block.gates).length +
            tail.liftedWord.length
        rw [hlifted]
        exact Nat.add_lt_add_left htail_lt _

/-- Terminal offsets, indexed in the same order as the requested Pauli labels,
as valid coordinates of the flattened physical word. -/
def TerminalBlockPrefixAssembly.terminalIndices
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    Fin labels.length → Fin assembly.liftedWord.length := fun i =>
  let offsetIndex : Fin assembly.terminalOffsets.length :=
    ⟨i.1, by
      rw [assembly.terminalOffsets_length_eq_labels_length]
      exact i.2⟩
  ⟨assembly.terminalOffsets.get offsetIndex,
    assembly.terminalOffset_lt_liftedWord_length
      (List.get_mem assembly.terminalOffsets offsetIndex)⟩

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
