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
