import GaloisForLFunctions.HTGeometry.TreePhaseTailCapacityLower

/-!
# Edge decomposition of the nested qubit path
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

def nestedMatchingEdge {L : ℕ} (j : Fin L) : Sym2 (PairQubit L) :=
  s((j, false), (j, true))

def nestedBridgeEdge {L : ℕ} (j : Fin (L - 1)) : Sym2 (PairQubit L) :=
  s((nestedBridgeLeft j, true), (nestedBridgeRight j, false))

theorem nestedMatchingEdge_injective {L : ℕ} :
    Function.Injective (@nestedMatchingEdge L) := by
  intro i j h
  rw [nestedMatchingEdge, nestedMatchingEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · exact congrArg Prod.fst h.1
  · have := congrArg Prod.snd h.1
    simp at this

theorem nestedBridgeEdge_injective {L : ℕ} :
    Function.Injective (@nestedBridgeEdge L) := by
  intro i j h
  rw [nestedBridgeEdge, nestedBridgeEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · have hv := congrArg (fun q => q.1.val) h.1
    simp [nestedBridgeLeft] at hv
    exact Fin.ext hv
  · have := congrArg Prod.snd h.1
    simp at this

theorem nestedMatchingEdge_ne_bridgeEdge {L : ℕ}
    (i : Fin L) (j : Fin (L - 1)) :
    nestedMatchingEdge i ≠ nestedBridgeEdge j := by
  intro h
  rw [nestedMatchingEdge, nestedBridgeEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · have := congrArg Prod.snd h.1
    simp at this
  · have h₁ := congrArg (fun q => q.1.val) h.1
    have h₂ := congrArg (fun q => q.1.val) h.2
    simp [nestedBridgeLeft, nestedBridgeRight] at h₁ h₂
    omega

def nestedMatchingEdges (L : ℕ) : Finset (Sym2 (PairQubit L)) :=
  Finset.univ.image nestedMatchingEdge

def nestedBridgeEdges (L : ℕ) : Finset (Sym2 (PairQubit L)) :=
  Finset.univ.image nestedBridgeEdge

@[simp] theorem mem_nestedMatchingEdges {L : ℕ} (e : Sym2 (PairQubit L)) :
    e ∈ nestedMatchingEdges L ↔ ∃ j : Fin L, nestedMatchingEdge j = e := by
  simp [nestedMatchingEdges]

@[simp] theorem mem_nestedBridgeEdges {L : ℕ} (e : Sym2 (PairQubit L)) :
    e ∈ nestedBridgeEdges L ↔ ∃ j : Fin (L - 1), nestedBridgeEdge j = e := by
  simp [nestedBridgeEdges]

@[simp] theorem nestedMatchingEdges_card (L : ℕ) :
    (nestedMatchingEdges L).card = L := by
  rw [nestedMatchingEdges, Finset.card_image_of_injective _ nestedMatchingEdge_injective]
  simp

@[simp] theorem nestedBridgeEdges_card (L : ℕ) :
    (nestedBridgeEdges L).card = L - 1 := by
  rw [nestedBridgeEdges, Finset.card_image_of_injective _ nestedBridgeEdge_injective]
  simp

theorem nestedMatchingEdges_disjoint_bridgeEdges (L : ℕ) :
    Disjoint (nestedMatchingEdges L) (nestedBridgeEdges L) := by
  rw [Finset.disjoint_left]
  intro e heM heB
  rcases (mem_nestedMatchingEdges e).mp heM with ⟨i, rfl⟩
  rcases (mem_nestedBridgeEdges (nestedMatchingEdge i)).mp heB with ⟨j, hj⟩
  exact nestedMatchingEdge_ne_bridgeEdge i j hj.symm

theorem nestedMatchingEdges_subset_path (L : ℕ) :
    nestedMatchingEdges L ⊆ (nestedQubitPathGraph L).edgeFinset := by
  intro e he
  rcases (mem_nestedMatchingEdges e).mp he with ⟨j, rfl⟩
  rw [SimpleGraph.mem_edgeFinset]
  change s((j, false), (j, true)) ∈ (nestedQubitPathGraph L).edgeSet
  rw [SimpleGraph.mem_edgeSet]
  exact nestedQubitPathGraph_adj_pair j

theorem nestedBridgeEdges_subset_path (L : ℕ) :
    nestedBridgeEdges L ⊆ (nestedQubitPathGraph L).edgeFinset := by
  intro e he
  rcases (mem_nestedBridgeEdges e).mp he with ⟨j, rfl⟩
  rw [SimpleGraph.mem_edgeFinset]
  change s((nestedBridgeLeft j, true), (nestedBridgeRight j, false)) ∈
    (nestedQubitPathGraph L).edgeSet
  rw [SimpleGraph.mem_edgeSet]
  exact nestedQubitPathGraph_adj_bridge j

/-- The path edge set is exactly the disjoint union of matching and bridge bonds. -/
theorem nestedPath_edgeFinset_eq_union {L : ℕ} (hL : 0 < L) :
    (nestedQubitPathGraph L).edgeFinset =
      nestedMatchingEdges L ∪ nestedBridgeEdges L := by
  apply Finset.Subset.antisymm
  · have hsub : nestedMatchingEdges L ∪ nestedBridgeEdges L ⊆
        (nestedQubitPathGraph L).edgeFinset :=
      Finset.union_subset (nestedMatchingEdges_subset_path L) (nestedBridgeEdges_subset_path L)
    have hcardUnion : (nestedMatchingEdges L ∪ nestedBridgeEdges L).card = 2 * L - 1 := by
      rw [Finset.card_union_of_disjoint (nestedMatchingEdges_disjoint_bridgeEdges L)]
      simp
      omega
    have hcardPath := (nestedQubitPathGraph_isTree hL).card_edgeFinset
    have hcardVertices : Fintype.card (PairQubit L) = 2 * L := by
      simp [PairQubit]
      omega
    rw [hcardVertices] at hcardPath
    have hcards : (nestedQubitPathGraph L).edgeFinset.card =
        (nestedMatchingEdges L ∪ nestedBridgeEdges L).card := by omega
    exact Finset.eq_of_subset_of_card_le hsub (by omega) |>.symm.subset
  · exact Finset.union_subset (nestedMatchingEdges_subset_path L)
      (nestedBridgeEdges_subset_path L)

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
