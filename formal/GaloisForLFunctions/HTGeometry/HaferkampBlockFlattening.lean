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

/-- Taking past an entire left word in an append retains that word and takes
the remaining number of entries from the right word. -/
theorem list_take_append_length_add
    {α : Type*} (left right : List α) (k : ℕ) :
    List.take (left.length + k) (left ++ right) = left ++ List.take k right := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- A `Fin` index shifted by the full left-word length reads the corresponding
entry of the right word. -/
theorem list_get_append_right
    {α : Type*} (left right : List α) (i : Fin right.length) :
    (left ++ right).get
      ⟨left.length + i.1, by
        rw [List.length_append]
        exact Nat.add_lt_add_left i.2 _⟩ = right.get i := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right (Nat.le_add_right _ _)]
  simp

/-- A coordinate within a left word reads the same entry after appending any
right word. -/
theorem list_get_append_left
    {α : Type*} (left right : List α) (i : Fin left.length) :
    (left ++ right).get
      ⟨i.1, by
        rw [List.length_append]
        exact lt_of_lt_of_le i.2 (Nat.le_add_right _ _)⟩ = left.get i := by
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left i.2]

/-- The successor index of a nonempty list reads the corresponding tail
entry without leaving a dependent `Fin` cast behind. -/
theorem list_get_cons_succ
    {α : Type*} (head : α) (tail : List α) (i : Fin tail.length) :
    (head :: tail).get (Fin.succ i) = tail.get i := rfl

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
  change (List.zipWith totalTwoQubitLift edges block.gates).reverse.prod = _
  rw [block.liftedWord_decomp_at (cone.mergePlan.terminal, root) block.edges_decomp,
    List.reverse_append, List.prod_append, List.reverse_cons, List.prod_append,
    suffix_lifted_reverse_prod_eq_one _ _ block.suffix_identity]
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
  let beforeProduct : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    (List.zipWith totalTwoQubitLift block.prefixEdges block.prefixGates).reverse.prod
  let terminalLift : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    totalTwoQubitLift (cone.mergePlan.terminal, root) block.terminalGate
  have hblock : edgeListBlockContraction edges block.gates = terminalLift * beforeProduct := by
    simpa only [beforeProduct, terminalLift] using block.contraction_eq_terminal_mul_prefix
  have hcoe := congrArg (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) hblock
  have hcoeMatrices :
      (edgeListBlockContraction edges block.gates :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := hcoe
  change Matrix.conjTranspose (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      Matrix.conjTranspose (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * Z *
      (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
    Matrix.conjTranspose (edgeListBlockContraction edges block.gates :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * Z *
      (edgeListBlockContraction edges block.gates :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
  rw [hcoeMatrices, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

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

/-- The nonzero scalar attached to each retained terminal coordinate, in the
same order as the requested Pauli labels. -/
def TerminalBlockPrefixAssembly.terminalCoefficients
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))} :
    TerminalBlockPrefixAssembly cone pre labels → List ℂ
  | .nil _ => []
  | .cons step tail =>
      (step.block.transportCoeff * step.prefixCoeff)⁻¹ :: tail.terminalCoefficients

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

/-- There is one retained nonzero scalar per requested Pauli label. -/
theorem TerminalBlockPrefixAssembly.terminalCoefficients_length_eq_labels_length
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    assembly.terminalCoefficients.length = labels.length := by
  induction assembly with
  | nil => rfl
  | cons step tail ih => simp [terminalCoefficients, ih]

/-- Every scalar retained from a terminal-aware block is nonzero. -/
theorem TerminalBlockPrefixAssembly.terminalCoefficient_ne_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) {c : ℂ}
    (hmem : c ∈ assembly.terminalCoefficients) : c ≠ 0 := by
  induction assembly with
  | nil => simp [terminalCoefficients] at hmem
  | cons step tail ih =>
      simp only [terminalCoefficients, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst c
        exact inv_ne_zero (mul_ne_zero step.block.transportCoeff_ne_zero step.prefixCoeff_ne_zero)
      · exact ih htail

/-- The scalar associated to a requested label, extracted from the terminal
coefficient word with the same finite index. -/
def TerminalBlockPrefixAssembly.terminalCoefficient
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) : ℂ :=
  assembly.terminalCoefficients.get ⟨i.1, by
    rw [assembly.terminalCoefficients_length_eq_labels_length]
    exact i.2⟩

/-- The scalar at every selected terminal coordinate is nonzero. -/
theorem TerminalBlockPrefixAssembly.terminalCoefficient_apply_ne_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) : assembly.terminalCoefficient i ≠ 0 := by
  unfold terminalCoefficient
  apply assembly.terminalCoefficient_ne_zero
  exact List.get_mem _ _

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
    Fin labels.length → Fin assembly.liftedWord.length := by
  induction assembly with
  | nil => exact Fin.elim0
  | cons step tail ih =>
      intro i
      refine Fin.cases ?_ ?_ i
      · refine ⟨step.block.prefixGates.length, ?_⟩
        have hlocal := step.block.prefixGates_length_lt_gates_length
        have hlifted :
            (List.zipWith totalTwoQubitLift edges step.block.gates).length =
              step.block.gates.length := by
          rw [List.length_zipWith]
          simp [step.block.gates_length]
        simp only [TerminalBlockPrefixAssembly.liftedWord, List.length_append]
        exact lt_of_lt_of_le (by simpa [hlifted] using hlocal) (Nat.le_add_right _ _)
      · intro j
        refine ⟨step.block.gates.length + (ih j).1, ?_⟩
        have hlifted :
            (List.zipWith totalTwoQubitLift edges step.block.gates).length =
              step.block.gates.length := by
          rw [List.length_zipWith]
          simp [step.block.gates_length]
        simp only [TerminalBlockPrefixAssembly.liftedWord, List.length_append]
        rw [hlifted]
        exact Nat.add_lt_add_left (ih j).2 _

/-- The full reverse-chronological prefix immediately before a selected
terminal coordinate, including the assembly's incoming Clifford prefix. -/
def TerminalBlockPrefixAssembly.terminalPrefix
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  (assembly.liftedWord.take (assembly.terminalIndices i).1).reverse.prod * pre

/-- The first label of a nonempty assembly selects the current block's
retained terminal position. -/
theorem TerminalBlockPrefixAssembly.terminalIndices_cons_zero_val
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps) :
    ((TerminalBlockPrefixAssembly.cons step tail).terminalIndices 0).1 =
      step.block.prefixGates.length := rfl

/-- Every later label selects the corresponding tail terminal coordinate,
shifted by the complete current block length. -/
theorem TerminalBlockPrefixAssembly.terminalIndices_cons_succ_val
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps)
    (i : Fin Ps.length) :
    ((TerminalBlockPrefixAssembly.cons step tail).terminalIndices (Fin.succ i)).1 =
      step.block.gates.length + (tail.terminalIndices i).1 := rfl

/-- The first terminal scalar is the stripped-coordinate scalar supplied by
the current block. -/
theorem TerminalBlockPrefixAssembly.terminalCoefficient_cons_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps) :
    (TerminalBlockPrefixAssembly.cons step tail).terminalCoefficient 0 =
      (step.block.transportCoeff * step.prefixCoeff)⁻¹ := rfl

/-- Later terminal scalars are exactly the recursively retained tail
scalars. -/
theorem TerminalBlockPrefixAssembly.terminalCoefficient_cons_succ
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps)
    (i : Fin Ps.length) :
    (TerminalBlockPrefixAssembly.cons step tail).terminalCoefficient (Fin.succ i) =
      tail.terminalCoefficient i := rfl

/-- The first terminal prefix is the selected local prefix followed by the
incoming Clifford prefix. -/
theorem TerminalBlockPrefixAssembly.terminalPrefix_cons_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps) :
    (TerminalBlockPrefixAssembly.cons step tail).terminalPrefix 0 =
      (List.zipWith totalTwoQubitLift step.block.prefixEdges step.block.prefixGates).reverse.prod *
        pre := by
  unfold terminalPrefix
  rw [TerminalBlockPrefixAssembly.terminalIndices_cons_zero_val]
  simp only [TerminalBlockPrefixAssembly.liftedWord]
  have hp : step.block.prefixGates.length ≤
      (List.zipWith totalTwoQubitLift edges step.block.gates).length := by
    have hlocal := step.block.prefixGates_length_lt_gates_length
    have hlifted : (List.zipWith totalTwoQubitLift edges step.block.gates).length =
        step.block.gates.length := by
      rw [List.length_zipWith]
      simp [step.block.gates_length]
    exact Nat.le_of_lt (by simpa [hlifted] using hlocal)
  rw [List.take_append_of_le_length hp, step.block.take_liftedWord_prefix]

/-- Every later terminal prefix is exactly its recursively indexed tail
prefix after the current full block has been executed. -/
theorem TerminalBlockPrefixAssembly.terminalPrefix_cons_succ
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps)
    (i : Fin Ps.length) :
    (TerminalBlockPrefixAssembly.cons step tail).terminalPrefix (Fin.succ i) =
      tail.terminalPrefix i := by
  unfold terminalPrefix
  rw [TerminalBlockPrefixAssembly.terminalIndices_cons_succ_val]
  simp only [TerminalBlockPrefixAssembly.liftedWord]
  have hlifted : (List.zipWith totalTwoQubitLift edges step.block.gates).length =
      step.block.gates.length := by
    rw [List.length_zipWith]
    simp [step.block.gates_length]
  rw [← hlifted, list_take_append_length_add, List.reverse_append, List.prod_append]
  change ((tail.liftedWord.take (tail.terminalIndices i).1).reverse.prod *
      edgeListBlockContraction edges step.block.gates) * pre =
    (tail.liftedWord.take (tail.terminalIndices i).1).reverse.prod *
      (edgeListBlockContraction edges step.block.gates * pre)
  exact mul_assoc _ _ _

/-- The first selected coordinate evaluates to the current block's lifted
terminal gate. -/
theorem TerminalBlockPrefixAssembly.terminalGate_cons_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps) :
    (TerminalBlockPrefixAssembly.cons step tail).liftedWord.get
      ((TerminalBlockPrefixAssembly.cons step tail).terminalIndices 0) =
      totalTwoQubitLift (cone.mergePlan.terminal, root) step.block.terminalGate := by
  let currentWord := List.zipWith totalTwoQubitLift edges step.block.gates
  let localIndex : Fin currentWord.length := ⟨step.block.prefixGates.length, by
    have hlocal := step.block.prefixGates_length_lt_gates_length
    have hlength : currentWord.length = step.block.gates.length := by
      dsimp [currentWord]
      rw [List.length_zipWith]
      simp [step.block.gates_length]
    exact (by simpa [hlength] using hlocal)⟩
  let globalIndex : Fin (currentWord ++ tail.liftedWord).length := ⟨localIndex.1, by
    rw [List.length_append]
    exact lt_of_lt_of_le localIndex.2 (Nat.le_add_right _ _)⟩
  have hindex : (TerminalBlockPrefixAssembly.cons step tail).terminalIndices 0 =
      globalIndex := Fin.ext (TerminalBlockPrefixAssembly.terminalIndices_cons_zero_val step tail)
  change (currentWord ++ tail.liftedWord).get
      ((TerminalBlockPrefixAssembly.cons step tail).terminalIndices 0) = _
  rw [hindex]
  calc
    (currentWord ++ tail.liftedWord).get globalIndex = currentWord.get localIndex := by
      exact list_get_append_left currentWord tail.liftedWord localIndex
    _ = totalTwoQubitLift (cone.mergePlan.terminal, root) step.block.terminalGate := by
      exact step.block.liftedWord_get_terminal

/-- A later selected coordinate evaluates to its recursively selected tail
gate. -/
theorem TerminalBlockPrefixAssembly.terminalGate_cons_succ
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)} {Ps : List (Fin n → Option (Fin 3))}
    (step : TerminalBlockPrefixStep cone pre P)
    (tail : TerminalBlockPrefixAssembly cone
      (edgeListBlockContraction edges step.block.gates * pre) Ps)
    (i : Fin Ps.length) :
    (TerminalBlockPrefixAssembly.cons step tail).liftedWord.get
      ((TerminalBlockPrefixAssembly.cons step tail).terminalIndices (Fin.succ i)) =
      tail.liftedWord.get (tail.terminalIndices i) := by
  let currentWord := List.zipWith totalTwoQubitLift edges step.block.gates
  let tailIndex := tail.terminalIndices i
  let globalIndex : Fin (currentWord ++ tail.liftedWord).length :=
    ⟨currentWord.length + tailIndex.1, by
      rw [List.length_append]
      exact Nat.add_lt_add_left tailIndex.2 _⟩
  have hlength : currentWord.length = step.block.gates.length := by
    dsimp [currentWord]
    rw [List.length_zipWith]
    simp [step.block.gates_length]
  have hindex : (TerminalBlockPrefixAssembly.cons step tail).terminalIndices (Fin.succ i) =
      globalIndex := Fin.ext (by
        rw [TerminalBlockPrefixAssembly.terminalIndices_cons_succ_val step tail i]
        simp [globalIndex, tailIndex, hlength])
  change (currentWord ++ tail.liftedWord).get
      ((TerminalBlockPrefixAssembly.cons step tail).terminalIndices (Fin.succ i)) =
    tail.liftedWord.get tailIndex
  rw [hindex]
  exact list_get_append_right currentWord tail.liftedWord tailIndex

/-- The step-level version of the terminal stripped-coordinate identity,
written directly in the local-prefix and terminal-gate coordinates. -/
theorem TerminalBlockPrefixStep.terminal_coordinate_stripped
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {P : Fin n → Option (Fin 3)}
    (step : TerminalBlockPrefixStep cone pre P) :
    Matrix.conjTranspose
        ((((List.zipWith totalTwoQubitLift step.block.prefixEdges step.block.prefixGates).reverse.prod *
          pre : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *
      Matrix.conjTranspose
        (totalTwoQubitLift (cone.mergePlan.terminal, root) step.block.terminalGate :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
      (totalTwoQubitLift (cone.mergePlan.terminal, root) step.block.terminalGate :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      ((((List.zipWith totalTwoQubitLift step.block.prefixEdges step.block.prefixGates).reverse.prod *
        pre : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) =
      (step.block.transportCoeff * step.prefixCoeff)⁻¹ • finitePauliMatrix P := by
  let beforeProduct : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    (List.zipWith totalTwoQubitLift step.block.prefixEdges step.block.prefixGates).reverse.prod
  let terminalLift : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    totalTwoQubitLift (cone.mergePlan.terminal, root) step.block.terminalGate
  let blockContraction : Matrix.unitaryGroup (Fin n → Bool) ℂ :=
    edgeListBlockContraction edges step.block.gates
  have hlocal := step.block.local_conjugation_eq_block_conjugation
    (finitePauliMatrix (Function.update (fun _ => none) root (some 2)))
  have hstripped := step.stripped_coordinate
  change Matrix.conjTranspose
      (((beforeProduct * pre : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *
      Matrix.conjTranspose (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
      (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      ((beforeProduct * pre : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
    (step.block.transportCoeff * step.prefixCoeff)⁻¹ • finitePauliMatrix P
  have hprefixCoe :
      ((beforeProduct * pre : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := rfl
  rw [hprefixCoe, Matrix.conjTranspose_mul]
  calc
    Matrix.conjTranspose (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        Matrix.conjTranspose (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        Matrix.conjTranspose (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
        (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      Matrix.conjTranspose (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (Matrix.conjTranspose (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          Matrix.conjTranspose (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
          (terminalLift : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          (beforeProduct : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *
        (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.conjTranspose (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (Matrix.conjTranspose (blockContraction : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
          finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
          (blockContraction : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *
        (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
        simpa only [beforeProduct, terminalLift, blockContraction] using
          congrArg (fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ =>
            Matrix.conjTranspose (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * M *
              (pre : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) hlocal
    _ = (step.block.transportCoeff * step.prefixCoeff)⁻¹ • finitePauliMatrix P := by
        simpa only [blockContraction] using hstripped

/-- At every recursively retained terminal gate, conjugating the root Pauli
through its literal flattened prefix recovers the corresponding fresh Pauli
direction, up to the stored nonzero scalar. -/
theorem TerminalBlockPrefixAssembly.terminalCoordinate_stripped
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (i : Fin labels.length) :
    Matrix.conjTranspose (assembly.terminalPrefix i :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      Matrix.conjTranspose (assembly.liftedWord.get (assembly.terminalIndices i) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      finitePauliMatrix (Function.update (fun _ => none) root (some 2)) *
      (assembly.liftedWord.get (assembly.terminalIndices i) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      (assembly.terminalPrefix i : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      assembly.terminalCoefficient i • finitePauliMatrix (labels.get i) := by
  induction assembly with
  | nil => exact Fin.elim0 i
  | @cons pre P Ps step tail ih =>
      refine Fin.cases ?_ ?_ i
      · rw [TerminalBlockPrefixAssembly.terminalPrefix_cons_zero step tail,
          TerminalBlockPrefixAssembly.terminalGate_cons_zero step tail,
          TerminalBlockPrefixAssembly.terminalCoefficient_cons_zero step tail]
        simpa only [List.get_cons_zero] using step.terminal_coordinate_stripped
      · intro j
        rw [TerminalBlockPrefixAssembly.terminalPrefix_cons_succ step tail j,
          TerminalBlockPrefixAssembly.terminalGate_cons_succ step tail j,
          TerminalBlockPrefixAssembly.terminalCoefficient_cons_succ step tail j]
        rw [list_get_cons_succ]
        exact ih j

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
