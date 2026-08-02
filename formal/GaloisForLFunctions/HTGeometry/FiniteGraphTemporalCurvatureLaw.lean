import GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite graph temporal curvature

This module formalizes the exact arithmetic set function attached to a
finite heterogeneous graph.  A connected component contributes its tensor
dimension minus one.  The resulting rank law gives interaction
multiplication, pair curvature, and the cancellation-free partition
curvature classifier.
-/

open Set SimpleGraph
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tensor dimension carried by one connected component. -/
def finiteGraphComponentDimension
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (C : G.ConnectedComponent) : ℕ :=
  ∏ v ∈ C.supp.toFinite.toFinset, localDimension v

/-- Generic projective temporal rank prescribed by connected-component
factorization of a finite heterogeneous graph. -/
def finiteGraphTemporalRank
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (localDimension : V → ℕ) : ℕ :=
  ∑ C : G.ConnectedComponent,
    (finiteGraphComponentDimension G localDimension C - 1)

/-- Vertices are exactly the connected components of the discrete graph. -/
def botConnectedComponentEquiv
    (V : Type*) :
    V ≃ (⊥ : SimpleGraph V).ConnectedComponent :=
  Equiv.ofBijective
    (⊥ : SimpleGraph V).connectedComponentMk ⟨by
      intro u v huv
      exact SimpleGraph.reachable_bot.mp
        (ConnectedComponent.exact huv), by
      intro C
      induction C using ConnectedComponent.ind with
      | _ v => exact ⟨v, rfl⟩⟩

/-- A discrete graph contributes the sum of its one-vertex ranks. -/
theorem finiteGraphTemporalRank_bot
    {V : Type*} [Fintype V]
    (localDimension : V → ℕ) :
    finiteGraphTemporalRank (⊥ : SimpleGraph V) localDimension =
      ∑ v, (localDimension v - 1) := by
  classical
  letI : Fintype ((⊥ : SimpleGraph V).ConnectedComponent) :=
    SetLike.instFintype
  unfold finiteGraphTemporalRank
  have hterm :
      ∀ v : V,
        localDimension v - 1 =
          finiteGraphComponentDimension
              (⊥ : SimpleGraph V) localDimension
              (botConnectedComponentEquiv V v) - 1 := by
    intro v
    unfold finiteGraphComponentDimension
    have hsupport :
        ((botConnectedComponentEquiv V v).supp : Set V) = {v} := by
      ext w
      simp [botConnectedComponentEquiv,
        ConnectedComponent.mem_supp_iff,
        ConnectedComponent.eq, SimpleGraph.reachable_bot]
    simp [hsupport]
  exact (Fintype.sum_equiv (botConnectedComponentEquiv V)
    (fun v => localDimension v - 1)
    (fun C => finiteGraphComponentDimension
      (⊥ : SimpleGraph V) localDimension C - 1)
    hterm).symm

/-- A connected graph contributes full tensor dimension minus global
phase. -/
theorem finiteGraphTemporalRank_of_connected
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (hG : G.Connected) :
    finiteGraphTemporalRank G localDimension =
      (∏ v, localDimension v) - 1 := by
  classical
  let root : V := Classical.arbitrary V
  let C₀ : G.ConnectedComponent := G.connectedComponentMk root
  letI : Subsingleton G.ConnectedComponent :=
    hG.preconnected.subsingleton_connectedComponent
  have hsupport : C₀.supp = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    rw [ConnectedComponent.mem_supp_iff]
    exact Subsingleton.elim _ _
  unfold finiteGraphTemporalRank
  rw [Finset.sum_eq_single C₀]
  · unfold finiteGraphComponentDimension
    simp [hsupport]
  · intro C _ hC
    exact (hC (Subsingleton.elim _ _)).elim
  · simp

/-- Connected interaction multiplication: temporal rank plus global phase
equals total tensor dimension. -/
theorem finiteGraphTemporalRank_add_one_of_connected
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (hlocal : ∀ v, 1 ≤ localDimension v)
    (hG : G.Connected) :
    finiteGraphTemporalRank G localDimension + 1 =
      ∏ v, localDimension v := by
  rw [finiteGraphTemporalRank_of_connected G localDimension hG]
  exact Nat.sub_add_cancel
    (show 1 ≤ ∏ v, localDimension v by
      exact Finset.one_le_prod (fun v _ => hlocal v))

/-- Product-minus-one rank under merging two connected components. -/
theorem temporalRank_merge_components
    (DA DB : ℕ) (hDA : 1 ≤ DA) (hDB : 1 ≤ DB) :
    DA * DB - 1 =
      (DA - 1) + (DB - 1) + (DA - 1) * (DB - 1) := by
  have hA : DA - 1 + 1 = DA := Nat.sub_add_cancel hDA
  have hB : DB - 1 + 1 = DB := Nat.sub_add_cancel hDB
  nth_rewrite 1 [← hA]
  nth_rewrite 1 [← hB]
  simp only [add_mul, mul_add, mul_one, one_mul]
  omega

/-- Exact temporal-dimension gain caused by merging two components. -/
theorem temporalRank_merge_gain
    (DA DB : ℕ) (hDA : 1 ≤ DA) (hDB : 1 ≤ DB) :
    (DA * DB - 1) - ((DA - 1) + (DB - 1)) =
      (DA - 1) * (DB - 1) := by
  rw [temporalRank_merge_components DA DB hDA hDB]
  omega

/-- Component-factorized temporal rank of an induced finite subgraph. -/
def finiteInducedGraphTemporalRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (S : Finset V) : ℕ :=
  finiteGraphTemporalRank
    (SimpleGraph.comap (fun v : S => v.1) G)
    (fun v : S => localDimension v.1)

theorem finiteInducedGraphTemporalRank_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (v : V) :
    finiteInducedGraphTemporalRank G localDimension {v} =
      localDimension v - 1 := by
  classical
  letI : Nonempty ({v} : Finset V) :=
    ⟨⟨v, by simp⟩⟩
  unfold finiteInducedGraphTemporalRank
  rw [finiteGraphTemporalRank_of_connected]
  · have hprod :
        (∏ x : ({v} : Finset V), localDimension x.1) =
          localDimension v := by
      rw [← Finset.prod_subtype ({v} : Finset V) (by simp)]
      simp
    rw [hprod]
  · exact SimpleGraph.Connected.of_subsingleton

private theorem induce_pair_eq_bot_of_not_adj
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (hnot : ¬ G.Adj u v) :
    SimpleGraph.comap (fun x : ({u, v} : Finset V) => x.1) G = ⊥ := by
  ext a b
  simp only [SimpleGraph.comap_adj, SimpleGraph.bot_adj, iff_false]
  intro hab
  have ha : a.1 = u ∨ a.1 = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using a.2
  have hb : b.1 = u ∨ b.1 = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using b.2
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb] at hab
    exact G.loopless.irrefl u hab
  · rw [ha, hb] at hab
    exact hnot hab
  · rw [ha, hb] at hab
    exact hnot hab.symm
  · rw [ha, hb] at hab
    exact G.loopless.irrefl v hab

private theorem induce_pair_connected_of_adj
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (hadj : G.Adj u v) :
    (SimpleGraph.comap
      (fun x : ({u, v} : Finset V) => x.1) G).Connected := by
  letI : Nonempty ({u, v} : Finset V) := ⟨⟨u, by simp⟩⟩
  refine ⟨?_⟩
  intro a b
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.refl a
  have ha : a.1 = u ∨ a.1 = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using a.2
  have hb : b.1 = u ∨ b.1 = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using b.2
  apply SimpleGraph.Adj.reachable
  change G.Adj a.1 b.1
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (Subtype.ext (ha.trans hb.symm))).elim
  · simpa [ha, hb] using hadj
  · simpa [ha, hb] using hadj.symm
  · exact (hab (Subtype.ext (ha.trans hb.symm))).elim

/-- Two-vertex induced rank is multiplicative on an edge and additive off
the edge. -/
theorem finiteInducedGraphTemporalRank_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (localDimension : V → ℕ)
    {u v : V} (huv : u ≠ v) :
    finiteInducedGraphTemporalRank G localDimension {u, v} =
      if G.Adj u v then
        localDimension u * localDimension v - 1
      else
        (localDimension u - 1) + (localDimension v - 1) := by
  classical
  by_cases hadj : G.Adj u v
  · rw [if_pos hadj]
    letI : Nonempty ({u, v} : Finset V) := ⟨⟨u, by simp⟩⟩
    unfold finiteInducedGraphTemporalRank
    rw [finiteGraphTemporalRank_of_connected
      (SimpleGraph.comap
        (fun x : ({u, v} : Finset V) => x.1) G)
      (fun x : ({u, v} : Finset V) => localDimension x.1)]
    · have hprod :
          (∏ x : ({u, v} : Finset V), localDimension x.1) =
            localDimension u * localDimension v := by
        rw [← Finset.prod_subtype ({u, v} : Finset V) (by simp)]
        simpa using (Finset.prod_pair (f := localDimension) huv)
      rw [hprod]
    · exact induce_pair_connected_of_adj hadj
  · rw [if_neg hadj]
    unfold finiteInducedGraphTemporalRank
    rw [induce_pair_eq_bot_of_not_adj hadj,
      finiteGraphTemporalRank_bot]
    change
      (∑ x : ({u, v} : Finset V), localDimension x.1 - 1) =
        (localDimension u - 1) + (localDimension v - 1)
    rw [Finset.univ_eq_attach, Finset.sum_attach]
    simp [huv]

/-- Pair temporal curvature of the component-factorized rank set
function. -/
def finiteGraphPairTemporalCurvature
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (localDimension : V → ℕ)
    (u v : V) : ℕ :=
  finiteInducedGraphTemporalRank G localDimension {u, v} -
    finiteInducedGraphTemporalRank G localDimension {u} -
    finiteInducedGraphTemporalRank G localDimension {v}

/-- **Pair temporal-curvature law.**  Distinct vertices have positive
curvature exactly across an interaction edge, with exact value
`(q_u - 1)(q_v - 1)`. -/
theorem finiteGraphPairTemporalCurvature_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (localDimension : V → ℕ)
    (hlocal : ∀ w, 1 ≤ localDimension w)
    {u v : V} (huv : u ≠ v) :
    finiteGraphPairTemporalCurvature G localDimension u v =
      if G.Adj u v then
        (localDimension u - 1) * (localDimension v - 1)
      else 0 := by
  classical
  unfold finiteGraphPairTemporalCurvature
  rw [finiteInducedGraphTemporalRank_pair G localDimension huv,
    finiteInducedGraphTemporalRank_singleton,
    finiteInducedGraphTemporalRank_singleton]
  by_cases hadj : G.Adj u v
  · simp only [if_pos hadj]
    rw [temporalRank_merge_components
      (localDimension u) (localDimension v) (hlocal u) (hlocal v)]
    omega
  · simp [hadj]

/-- Temporal curvature reconstructs adjacency when every local dimension
is at least two. -/
theorem adj_iff_finiteGraphPairTemporalCurvature_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (localDimension : V → ℕ)
    (hlocal : ∀ w, 2 ≤ localDimension w)
    {u v : V} (huv : u ≠ v) :
    G.Adj u v ↔
      0 < finiteGraphPairTemporalCurvature
        G localDimension u v := by
  rw [finiteGraphPairTemporalCurvature_eq G localDimension
    (fun w => le_trans (by omega) (hlocal w)) huv]
  by_cases hadj : G.Adj u v
  · simp only [hadj, if_true, true_iff]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two (hlocal u)))
      (Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two (hlocal v)))
  · simp [hadj]

end

end GaloisForLFunctions.HTGeometry
