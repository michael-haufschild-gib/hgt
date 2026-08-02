import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Anchored replica graph

Copies of one connected graph are placed on every layer of a finite or
infinite alphabet.  One bridge from each nonanchor layer to the anchor copy
connects the whole replica graph.  Any nonbipartite anchor copy forces the
whole graph to remain nonbipartite.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Layer replicas of `G`, with one selected bridge from every nonanchor
layer to the anchor layer. -/
def anchoredReplicaGraph
    {I ρ : Type*} (G : SimpleGraph I) (anchor : ρ)
    (source target : ρ → I) :
    SimpleGraph (I × ρ) where
  Adj x y :=
    (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨
      ∃ r, r ≠ anchor ∧
        ((x = (source r, r) ∧ y = (target r, anchor)) ∨
          (y = (source r, r) ∧ x = (target r, anchor)))
  symm := by
    constructor
    intro x y hxy
    rcases hxy with hsame | ⟨r, hr, hcross⟩
    · exact Or.inl ⟨hsame.1.symm, hsame.2.symm⟩
    · exact Or.inr ⟨r, hr, hcross.elim Or.inr Or.inl⟩
  loopless := by
    constructor
    intro x hxx
    rcases hxx with hsame | ⟨r, hr, hcross⟩
    · exact hsame.2.ne rfl
    · rcases hcross with hcross | hcross
      · exact hr (congrArg Prod.snd (hcross.1.symm.trans hcross.2))
      · exact hr (congrArg Prod.snd (hcross.1.symm.trans hcross.2))

@[simp] theorem anchoredReplicaGraph_adj
    {I ρ : Type*} (G : SimpleGraph I) (anchor : ρ)
    (source target : ρ → I) (x y : I × ρ) :
    (anchoredReplicaGraph G anchor source target).Adj x y ↔
      (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨
        ∃ r, r ≠ anchor ∧
          ((x = (source r, r) ∧ y = (target r, anchor)) ∨
            (y = (source r, r) ∧ x = (target r, anchor))) :=
  Iff.rfl

/-- Every layer copy of the base graph maps homomorphically into the
anchored replica graph. -/
def anchoredReplicaGraphLayerHom
    {I ρ : Type*} (G : SimpleGraph I) (anchor layer : ρ)
    (source target : ρ → I) :
    G →g anchoredReplicaGraph G anchor source target where
  toFun i := (i, layer)
  map_rel' := fun hij => Or.inl ⟨rfl, hij⟩

/-- A connected base graph plus one bridge from every nonanchor layer makes
the entire anchored replica graph connected. -/
theorem anchoredReplicaGraph_preconnected
    {I ρ : Type*} [Nonempty I]
    (G : SimpleGraph I) (hG : G.Preconnected)
    (anchor : ρ) (source target : ρ → I) :
    (anchoredReplicaGraph G anchor source target).Preconnected := by
  let center : I := Classical.choice (inferInstance : Nonempty I)
  have hToAnchor :
      ∀ x : I × ρ,
        (anchoredReplicaGraph G anchor source target).Reachable
          x (center, anchor) := by
    rintro ⟨i, r⟩
    by_cases hr : r = anchor
    · subst r
      exact (hG i center).map
        (anchoredReplicaGraphLayerHom
          G anchor anchor source target)
    · have hwithin :
          (anchoredReplicaGraph G anchor source target).Reachable
            (i, r) (source r, r) :=
        (hG i (source r)).map
          (anchoredReplicaGraphLayerHom
            G anchor r source target)
      have hbridge :
          (anchoredReplicaGraph G anchor source target).Reachable
            (source r, r) (target r, anchor) := by
        apply SimpleGraph.Adj.reachable
        exact Or.inr ⟨r, hr, Or.inl ⟨rfl, rfl⟩⟩
      have hanchor :
          (anchoredReplicaGraph G anchor source target).Reachable
            (target r, anchor) (center, anchor) :=
        (hG (target r) center).map
          (anchoredReplicaGraphLayerHom
            G anchor anchor source target)
      exact hwithin.trans (hbridge.trans hanchor)
  intro x y
  exact (hToAnchor x).trans (hToAnchor y).symm

/-- A nonbipartite base graph remains nonbipartite after arbitrary anchored
replication and bridging. -/
theorem anchoredReplicaGraph_not_isBipartite
    {I ρ : Type*}
    (G : SimpleGraph I) (hG : ¬ G.IsBipartite)
    (anchor : ρ) (source target : ρ → I) :
    ¬ (anchoredReplicaGraph G anchor source target).IsBipartite := by
  intro hreplica
  apply hG
  rcases hreplica with ⟨coloring⟩
  exact ⟨coloring.comap
    (anchoredReplicaGraphLayerHom
      G anchor anchor source target)⟩

/-- Any supergraph containing a connected anchored replica graph is
connected. -/
theorem preconnected_of_anchoredReplicaGraph_le
    {I ρ : Type*} [Nonempty I]
    (G : SimpleGraph I) (hG : G.Preconnected)
    (anchor : ρ) (source target : ρ → I)
    (H : SimpleGraph (I × ρ))
    (hle : anchoredReplicaGraph G anchor source target ≤ H) :
    H.Preconnected := by
  intro x y
  exact SimpleGraph.Reachable.mono hle
    (anchoredReplicaGraph_preconnected
      G hG anchor source target x y)

/-- Any supergraph containing a nonbipartite anchored replica graph remains
nonbipartite. -/
theorem not_isBipartite_of_anchoredReplicaGraph_le
    {I ρ : Type*}
    (G : SimpleGraph I) (hG : ¬ G.IsBipartite)
    (anchor : ρ) (source target : ρ → I)
    (H : SimpleGraph (I × ρ))
    (hle : anchoredReplicaGraph G anchor source target ≤ H) :
    ¬ H.IsBipartite := by
  intro hH
  exact
    anchoredReplicaGraph_not_isBipartite
      G hG anchor source target
      (SimpleGraph.Colorable.mono_left hle hH)

end GaloisForLFunctions.HTGeometry
