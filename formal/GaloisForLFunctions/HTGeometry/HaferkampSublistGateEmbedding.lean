import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture

/-!
# Identity extension of an ordered subword of local gates

Appendix B chooses gates only on a light-cone subword.  A paper block still
contains every original location, so this generic certificate fills skipped
locations with an identity gate and proves that the ordered product is
unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A position-preserving extension of selected gate values from an ordered
subword into a larger word; every skipped position receives `default`. -/
inductive HaferkampGateWordEmbedding {α : Type*} {β : Type*} (default : β) :
    List α → List β → List α → List β → Prop
  | nil : HaferkampGateWordEmbedding default [] [] [] []
  | skip {e : α} {selectedEdges : List α} {selectedGates : List β}
      {blockEdges : List α} {blockGates : List β} :
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates →
        HaferkampGateWordEmbedding default selectedEdges selectedGates
          (e :: blockEdges) (default :: blockGates)
  | take {e : α} {gate : β} {selectedEdges : List α} {selectedGates : List β}
      {blockEdges : List α} {blockGates : List β} :
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates →
        HaferkampGateWordEmbedding default (e :: selectedEdges) (gate :: selectedGates)
          (e :: blockEdges) (gate :: blockGates)

/-- Every ordinary list sublist extends any aligned selected gate word by
identity values. -/
theorem exists_haferkampGateWordEmbedding
    {α : Type*} {β : Type*} (default : β)
    {selectedEdges blockEdges : List α} (hsub : selectedEdges.Sublist blockEdges)
    (selectedGates : List β) (hlen : selectedGates.length = selectedEdges.length) :
    ∃ blockGates,
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates := by
  induction hsub generalizing selectedGates with
  | slnil =>
      cases selectedGates with
      | nil => exact ⟨[], .nil⟩
      | cons gate selectedGates => simp at hlen
  | cons e hsub ih =>
      obtain ⟨blockGates, hgate⟩ := ih selectedGates hlen
      exact ⟨default :: blockGates, .skip hgate⟩
  | cons_cons e hsub ih =>
      cases selectedGates with
      | nil => simp at hlen
      | cons gate selectedGates =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          obtain ⟨blockGates, hgate⟩ := ih selectedGates hlen
          exact ⟨gate :: blockGates, .take hgate⟩

/-- Every embedding provides one gate value for every block location. -/
theorem HaferkampGateWordEmbedding.blockGates_length_eq
    {α : Type*} {β : Type*} {default : β}
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding :
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates) :
    blockGates.length = blockEdges.length := by
  induction embedding with
  | nil => rfl
  | skip h ih => simpa using congrArg Nat.succ ih
  | take h ih => simpa using congrArg Nat.succ ih

/-- Selected and selected-gate words in an embedding have equal lengths. -/
theorem HaferkampGateWordEmbedding.selectedGates_length_eq_selectedEdges_length
    {α : Type*} {β : Type*} {default : β}
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding : HaferkampGateWordEmbedding default
      selectedEdges selectedGates blockEdges blockGates) :
    selectedGates.length = selectedEdges.length := by
  induction embedding with
  | nil => rfl
  | skip h ih => exact ih
  | take h ih => simpa using congrArg Nat.succ ih

/-- An embedding with no selected locations assigns the default gate at every
physical block location. -/
theorem HaferkampGateWordEmbedding.all_blockGates_eq_default_of_empty
    {α : Type*} {β : Type*} {default : β}
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding : HaferkampGateWordEmbedding default
      selectedEdges selectedGates blockEdges blockGates)
    (hEdges : selectedEdges = []) (hGates : selectedGates = []) :
    ∀ gate ∈ blockGates, gate = default := by
  induction embedding with
  | nil => simp
  | skip h ih =>
      intro gate hgate
      simp only [List.mem_cons] at hgate
      rcases hgate with rfl | hgate
      · rfl
      · exact ih hEdges hGates gate hgate
  | take h ih => simp at hEdges

/-- If selected edge and gate words end in a specified terminal pair, their
physical embedding has one matching occurrence after which every remaining
physical gate is the default. -/
theorem HaferkampGateWordEmbedding.terminal_gate_suffix
    {α : Type*} {β : Type*} {default : β}
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding : HaferkampGateWordEmbedding default
      selectedEdges selectedGates blockEdges blockGates)
    {terminalEdge : α} {terminalGate : β}
    (hEdges : ∃ beforeEdges, selectedEdges = beforeEdges ++ [terminalEdge])
    (hGates : ∃ beforeGates, selectedGates = beforeGates ++ [terminalGate]) :
    ∃ beforeBlockEdges afterBlockEdges beforeBlockGates afterBlockGates,
      blockEdges = beforeBlockEdges ++ terminalEdge :: afterBlockEdges ∧
      blockGates = beforeBlockGates ++ terminalGate :: afterBlockGates ∧
      beforeBlockGates.length = beforeBlockEdges.length ∧
      afterBlockGates.length = afterBlockEdges.length ∧
      ∀ gate ∈ afterBlockGates, gate = default := by
  induction embedding generalizing terminalEdge terminalGate with
  | nil =>
      rcases hEdges with ⟨beforeEdges, hEdges⟩
      simp at hEdges
  | @skip e selectedEdges selectedGates blockEdges blockGates h ih =>
      obtain ⟨beforeBlockEdges, afterBlockEdges, beforeBlockGates, afterBlockGates,
        hblockEdges, hblockGates, hbeforeLength, hafterLength, hdefault⟩ := ih hEdges hGates
      refine ⟨e :: beforeBlockEdges, afterBlockEdges,
        default :: beforeBlockGates, afterBlockGates, ?_, ?_, ?_, hafterLength, hdefault⟩
      · simp [hblockEdges]
      · simp [hblockGates]
      · simpa using congrArg Nat.succ hbeforeLength
  | @take e gate selectedEdges selectedGates blockEdges blockGates h ih =>
      cases selectedEdges with
      | nil =>
          rcases hEdges with ⟨beforeEdges, hEdges⟩
          have hbeforeEdges : beforeEdges = [] := by
            cases beforeEdges with
            | nil => rfl
            | cons firstEdge beforeEdges =>
                simp only [List.cons_append, List.cons.injEq] at hEdges
                simp at hEdges
          subst beforeEdges
          simp only [List.nil_append, List.cons.injEq] at hEdges
          have hselectedGates : selectedGates = [] := by
            have hlength := selectedGates_length_eq_selectedEdges_length h
            apply List.eq_nil_of_length_eq_zero
            simpa using hlength
          subst selectedGates
          rcases hGates with ⟨beforeGates, hGates⟩
          have hbeforeGates : beforeGates = [] := by
            cases beforeGates with
            | nil => rfl
            | cons firstGate beforeGates =>
                simp only [List.cons_append, List.cons.injEq] at hGates
                simp at hGates
          subst beforeGates
          simp only [List.nil_append, List.cons.injEq] at hGates
          refine ⟨[], blockEdges, [], blockGates, ?_, ?_, rfl,
            h.blockGates_length_eq, ?_⟩
          · simp [hEdges]
          · simp [hGates]
          · exact all_blockGates_eq_default_of_empty h rfl rfl
      | cons nextEdge selectedEdges =>
          have hEdgesTail : ∃ beforeEdges,
              nextEdge :: selectedEdges = beforeEdges ++ [terminalEdge] := by
            rcases hEdges with ⟨beforeEdges, hEdges⟩
            cases beforeEdges with
            | nil =>
                simp only [List.nil_append] at hEdges
                cases hEdges
            | cons firstEdge beforeEdges =>
                simp only [List.cons_append, List.cons.injEq] at hEdges
                exact ⟨beforeEdges, hEdges.2⟩
          have hGatesTail : ∃ beforeGates,
              selectedGates = beforeGates ++ [terminalGate] := by
            rcases hGates with ⟨beforeGates, hGates⟩
            cases beforeGates with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at hGates
                have hselectedLength := selectedGates_length_eq_selectedEdges_length h
                rw [hGates.2] at hselectedLength
                simp at hselectedLength
            | cons firstGate beforeGates =>
                simp only [List.cons_append, List.cons.injEq] at hGates
                exact ⟨beforeGates, hGates.2⟩
          obtain ⟨beforeBlockEdges, afterBlockEdges, beforeBlockGates,
            afterBlockGates, hblockEdges, hblockGates, hbeforeLength,
            hafterLength, hdefault⟩ :=
            ih hEdgesTail hGatesTail
          refine ⟨e :: beforeBlockEdges, afterBlockEdges,
            gate :: beforeBlockGates, afterBlockGates, ?_, ?_, ?_, hafterLength, hdefault⟩
          · simp [hblockEdges]
          · simp [hblockGates]
          · simpa using congrArg Nat.succ hbeforeLength

/-- Product of local gate interpretations along an ordered edge word. -/
def haferkampGateWordProduct {α : Type*} {β : Type*} {G : Type*} [Monoid G]
    (lift : α → β → G) (edges : List α) (gates : List β) : G :=
  (List.zipWith lift edges gates).prod

/-- Filling all skipped positions with a gate whose interpretation is the
identity preserves the exact ordered product. -/
theorem HaferkampGateWordEmbedding.product_eq
    {α : Type*} {β : Type*} {G : Type*} [Monoid G] {default : β}
    {lift : α → β → G} (hdefault : ∀ edge, lift edge default = 1)
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding :
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates) :
    haferkampGateWordProduct lift blockEdges blockGates =
      haferkampGateWordProduct lift selectedEdges selectedGates := by
  induction embedding with
  | nil => rfl
  | skip h ih =>
      simpa [haferkampGateWordProduct, hdefault] using ih
  | take h ih =>
      simpa [haferkampGateWordProduct] using congrArg (fun z => lift _ _ * z) ih

/-- Reverse-chronological product of local gate interpretations.  This is the
matrix multiplication order for a word whose list order is execution order. -/
def haferkampGateWordReverseProduct
    {α : Type*} {β : Type*} {G : Type*} [Monoid G]
  (lift : α → β → G) (edges : List α) (gates : List β) : G :=
  (List.zipWith lift edges gates).reverse.prod

/-- One selected head gate is applied after the reverse-chronological product
of all later locations. -/
theorem haferkampGateWordReverseProduct_cons
    {α : Type*} {β : Type*} {G : Type*} [Monoid G]
    (lift : α → β → G) (edge : α) (gate : β)
    (edges : List α) (gates : List β) :
    haferkampGateWordReverseProduct lift (edge :: edges) (gate :: gates) =
      haferkampGateWordReverseProduct lift edges gates * lift edge gate := by
  simp [haferkampGateWordReverseProduct]

/-- Splitting two aligned chronological words reverses their product order. -/
theorem haferkampGateWordReverseProduct_append
    {α : Type*} {β : Type*} {G : Type*} [Monoid G]
    (lift : α → β → G)
    (leftEdges rightEdges : List α) (leftGates rightGates : List β)
    (hleft : leftEdges.length = leftGates.length) :
    haferkampGateWordReverseProduct lift (leftEdges ++ rightEdges)
      (leftGates ++ rightGates) =
      haferkampGateWordReverseProduct lift rightEdges rightGates *
        haferkampGateWordReverseProduct lift leftEdges leftGates := by
  rw [haferkampGateWordReverseProduct, List.zipWith_append hleft,
    List.reverse_append, List.prod_append]
  rfl

/-- Identity extension also preserves the reverse-chronological product used
by the circuit contraction map. -/
theorem HaferkampGateWordEmbedding.reverseProduct_eq
    {α : Type*} {β : Type*} {G : Type*} [Monoid G] {default : β}
    {lift : α → β → G} (hdefault : ∀ edge, lift edge default = 1)
    {selectedEdges : List α} {selectedGates : List β}
    {blockEdges : List α} {blockGates : List β}
    (embedding :
      HaferkampGateWordEmbedding default selectedEdges selectedGates blockEdges blockGates) :
    haferkampGateWordReverseProduct lift blockEdges blockGates =
      haferkampGateWordReverseProduct lift selectedEdges selectedGates := by
  induction embedding with
  | nil => rfl
  | skip h ih =>
      simpa [haferkampGateWordReverseProduct, hdefault] using ih
  | take h ih =>
      simpa [haferkampGateWordReverseProduct] using
        congrArg (fun z => z * lift _ _) ih

end GaloisForLFunctions.HTGeometry
