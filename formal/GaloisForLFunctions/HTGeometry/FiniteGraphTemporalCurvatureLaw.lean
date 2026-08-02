import GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.Partition.Finpartition

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
  @finiteGraphTemporalRank S (Finset.fintypeCoeSort S)
    (SimpleGraph.comap (fun v : S => v.1) G)
    (fun v : S => localDimension v.1)

theorem finiteInducedGraphTemporalRank_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (v : V) :
    finiteInducedGraphTemporalRank G localDimension {v} =
      localDimension v - 1 := by
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
    calc
      (∑ x : ({u, v} : Finset V), (localDimension x.1 - 1)) =
          ∑ x ∈ ({u, v} : Finset V), (localDimension x - 1) := by
        exact (Finset.sum_subtype
          (p := fun x : V => x ∈ ({u, v} : Finset V))
          ({u, v} : Finset V) (fun _ => Iff.rfl)
          (fun x => localDimension x - 1)).symm
      _ = (localDimension u - 1) + (localDimension v - 1) := by
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

/-- Product-minus-one dominates the sum of the factorwise
product-minus-one ranks. -/
theorem sum_sub_one_le_prod_sub_one
    {I : Type*} [DecidableEq I]
    (s : Finset I) (dimension : I → ℕ)
    (hdimension : ∀ i ∈ s, 1 ≤ dimension i) :
    ∑ i ∈ s, (dimension i - 1) ≤
      (∏ i ∈ s, dimension i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hda : 1 ≤ dimension a := hdimension a (by simp)
      have hds : ∀ i ∈ s, 1 ≤ dimension i := by
        intro i hi
        exact hdimension i (by simp [hi])
      have hp : 1 ≤ ∏ i ∈ s, dimension i :=
        Finset.one_le_prod hds
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        temporalRank_merge_components (dimension a)
          (∏ i ∈ s, dimension i) hda hp]
      have hi := ih hds
      omega

/-- The product-minus-one inequality is strict as soon as at least two
nontrivial factors are present. -/
theorem sum_sub_one_lt_prod_sub_one_of_one_lt_card
    {I : Type*} [DecidableEq I]
    (s : Finset I) (dimension : I → ℕ)
    (hdimension : ∀ i ∈ s, 2 ≤ dimension i)
    (hcard : 1 < s.card) :
    ∑ i ∈ s, (dimension i - 1) <
      (∏ i ∈ s, dimension i) - 1 := by
  obtain ⟨a, ha⟩ := s.nonempty_of_ne_empty (by
    intro hs
    simp [hs] at hcard)
  let t := s.erase a
  have ht : t.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro ht
    have hsubset : s ⊆ {a} := by
      intro i hi
      by_cases hia : i = a
      · simp [hia]
      · have : i ∈ t := by simp [t, hi, hia]
        simp [ht] at this
    have : s.card ≤ 1 := by
      simpa using Finset.card_le_card hsubset
    omega
  have hda : 1 ≤ dimension a :=
    le_trans (by omega) (hdimension a ha)
  have hdt : ∀ i ∈ t, 1 ≤ dimension i := by
    intro i hi
    exact le_trans (by omega)
      (hdimension i (Finset.mem_of_mem_erase hi))
  have hp_one : 1 ≤ ∏ i ∈ t, dimension i :=
    Finset.one_le_prod hdt
  obtain ⟨b, hb⟩ := ht
  have hp_two : 2 ≤ ∏ i ∈ t, dimension i := by
    have hrest : 1 ≤ ∏ i ∈ t.erase b, dimension i :=
      Finset.one_le_prod (by
        intro i hi
        exact hdt i (Finset.mem_of_mem_erase hi))
    calc
      2 = 2 * 1 := by omega
      _ ≤ dimension b * (∏ i ∈ t.erase b, dimension i) :=
        Nat.mul_le_mul (hdimension b
          (Finset.mem_of_mem_erase hb)) hrest
      _ = ∏ i ∈ t, dimension i := by
        rw [← Finset.prod_insert (s := t.erase b)
          (f := dimension) (by simp),
          Finset.insert_erase hb]
  have hcoarse := temporalRank_merge_components
    (dimension a) (∏ i ∈ t, dimension i) hda hp_one
  have hfine := sum_sub_one_le_prod_sub_one t dimension hdt
  have hgain :
      0 < (dimension a - 1) *
        ((∏ i ∈ t, dimension i) - 1) := by
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two
        (hdimension a ha)))
      (Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two hp_two))
  have hs : insert a t = s := by
    exact Finset.insert_erase ha
  rw [← hs, Finset.sum_insert (by simp [t]),
    Finset.prod_insert (by simp [t]), hcoarse]
  omega

/-- Tensor-rank weight of a finite set partition. -/
def finpartitionTensorRank
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P : Finpartition S) (localDimension : V → ℕ) : ℕ :=
  ∑ B ∈ P.parts,
    ((∏ v ∈ B, localDimension v) - 1)

private theorem two_le_prod_of_nonempty
    {I : Type*} [DecidableEq I]
    (s : Finset I) (dimension : I → ℕ)
    (hdimension : ∀ i ∈ s, 2 ≤ dimension i)
    (hs : s.Nonempty) :
    2 ≤ ∏ i ∈ s, dimension i := by
  obtain ⟨a, ha⟩ := hs
  have hrest : 1 ≤ ∏ i ∈ s.erase a, dimension i :=
    Finset.one_le_prod (by
      intro i hi
      exact le_trans (by omega)
        (hdimension i (Finset.mem_of_mem_erase hi)))
  calc
    2 = 2 * 1 := by omega
    _ ≤ dimension a * (∏ i ∈ s.erase a, dimension i) :=
      Nat.mul_le_mul (hdimension a ha) hrest
    _ = ∏ i ∈ s, dimension i := by
      rw [← Finset.prod_insert (s := s.erase a)
        (f := dimension) (by simp), Finset.insert_erase ha]

private theorem finpartition_product_parts
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P : Finpartition S) (localDimension : V → ℕ) :
    ∏ v ∈ S, localDimension v =
      ∏ B ∈ P.parts, (∏ v ∈ B, localDimension v) := by
  calc
    (∏ v ∈ S, localDimension v) =
        ∏ v ∈ P.parts.biUnion id, localDimension v := by
      exact (congrArg (fun T : Finset V =>
        ∏ v ∈ T, localDimension v) P.biUnion_parts).symm
    _ = ∏ B ∈ P.parts, (∏ v ∈ B, localDimension v) :=
      Finset.prod_biUnion P.disjoint

/-- Refining a nonempty tensor block into subblocks cannot increase its
component-factorized temporal rank. -/
theorem finpartitionTensorRank_le
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P : Finpartition S) (localDimension : V → ℕ)
    (hlocal : ∀ v ∈ S, 2 ≤ localDimension v) :
    finpartitionTensorRank P localDimension ≤
      (∏ v ∈ S, localDimension v) - 1 := by
  unfold finpartitionTensorRank
  rw [finpartition_product_parts P localDimension]
  apply sum_sub_one_le_prod_sub_one P.parts
    (fun B => ∏ v ∈ B, localDimension v)
  intro B hB
  exact le_trans (by omega) (two_le_prod_of_nonempty B localDimension
    (fun v hv => hlocal v (P.subset hB hv))
    (P.nonempty_of_mem_parts hB))

/-- The refinement inequality is strict exactly when a tensor block is
split into at least two nonempty parts. -/
theorem finpartitionTensorRank_lt_of_one_lt_card
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P : Finpartition S) (localDimension : V → ℕ)
    (hlocal : ∀ v ∈ S, 2 ≤ localDimension v)
    (hcard : 1 < P.parts.card) :
    finpartitionTensorRank P localDimension <
      (∏ v ∈ S, localDimension v) - 1 := by
  unfold finpartitionTensorRank
  rw [finpartition_product_parts P localDimension]
  apply sum_sub_one_lt_prod_sub_one_of_one_lt_card P.parts
    (fun B => ∏ v ∈ B, localDimension v) _ hcard
  intro B hB
  exact two_le_prod_of_nonempty B localDimension
    (fun v hv => hlocal v (P.subset hB hv))
    (P.nonempty_of_mem_parts hB)

/-- Equality in the refinement inequality occurs exactly for a one-part
partition. -/
theorem finpartitionTensorRank_eq_iff_card_parts_eq_one
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P : Finpartition S) (localDimension : V → ℕ)
    (hS : S.Nonempty)
    (hlocal : ∀ v ∈ S, 2 ≤ localDimension v) :
    finpartitionTensorRank P localDimension =
        (∏ v ∈ S, localDimension v) - 1 ↔
      P.parts.card = 1 := by
  constructor
  · intro heq
    have hparts : P.parts.Nonempty :=
      P.parts_nonempty (by simpa using hS.ne_empty)
    have hcard_one : 1 ≤ P.parts.card :=
      Finset.one_le_card.mpr hparts
    by_contra hne
    have hcard : 1 < P.parts.card := by omega
    have hlt := finpartitionTensorRank_lt_of_one_lt_card
      P localDimension hlocal hcard
    omega
  · intro hcard
    obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hcard
    have hBS : B = S := by
      have hcover := P.biUnion_parts
      simpa [hparts] using hcover
    simp [finpartitionTensorRank, hparts, hBS]

/-- Finite partition of the vertex set into graph connected components. -/
noncomputable def graphConnectedFinpartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid G.reachableSetoid

/-- The part containing a vertex is exactly the support of its connected
component. -/
theorem graphConnectedFinpartition_part_eq_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) :
    (graphConnectedFinpartition G).part v =
      (G.connectedComponentMk v).supp.toFinite.toFinset := by
  classical
  ext w
  rw [graphConnectedFinpartition,
    Finpartition.mem_part_ofSetoid_iff_rel]
  rw [(G.connectedComponentMk v).supp.toFinite.mem_toFinset,
    ConnectedComponent.mem_supp_iff]
  rw [ConnectedComponent.eq, G.reachable_comm]
  change G.Reachable v w ↔ G.Reachable v w
  rfl

/-- Connected components are canonically equivalent to parts of the
connected-component finpartition. -/
noncomputable def connectedComponentEquivGraphPartitionPart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    G.ConnectedComponent ≃ (graphConnectedFinpartition G).parts := by
  classical
  let toPart : G.ConnectedComponent →
      (graphConnectedFinpartition G).parts := fun C =>
    ⟨C.supp.toFinite.toFinset, by
      induction C using ConnectedComponent.ind with
      | _ v =>
          rw [← graphConnectedFinpartition_part_eq_support G v]
          exact (graphConnectedFinpartition G).part_mem.mpr
            (Finset.mem_univ v)⟩
  apply Equiv.ofBijective toPart
  constructor
  · intro C D hCD
    induction C using ConnectedComponent.ind with
    | _ v =>
      have hfin :
          (G.connectedComponentMk v).supp.toFinite.toFinset =
            D.supp.toFinite.toFinset := by
        have := congrArg Subtype.val hCD
        simpa [toPart] using this
      have hv : v ∈ D.supp.toFinite.toFinset := by
        have hvself :
            v ∈ (G.connectedComponentMk v).supp.toFinite.toFinset := by
          rw [(G.connectedComponentMk v).supp.toFinite.mem_toFinset,
            ConnectedComponent.mem_supp_iff]
        rwa [← hfin]
      exact (ConnectedComponent.mem_supp_iff D v).mp
        (D.supp.toFinite.mem_toFinset.mp hv)
  · intro B
    obtain ⟨v, hv⟩ :=
      (graphConnectedFinpartition G).nonempty_of_mem_parts B.2
    refine ⟨G.connectedComponentMk v, ?_⟩
    apply Subtype.ext
    change (G.connectedComponentMk v).supp.toFinite.toFinset = B.1
    rw [← graphConnectedFinpartition_part_eq_support G v]
    exact (graphConnectedFinpartition G).part_eq_of_mem B.2 hv

/-- The connected-component formula is exactly the tensor-rank weight of
the connected-component partition. -/
theorem finiteGraphTemporalRank_eq_finpartitionTensorRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ) :
    finiteGraphTemporalRank G localDimension =
      finpartitionTensorRank
        (graphConnectedFinpartition G) localDimension := by
  classical
  letI : Fintype G.ConnectedComponent := SetLike.instFintype
  let P := graphConnectedFinpartition G
  let e := connectedComponentEquivGraphPartitionPart G
  have hsum :
      (∑ C : G.ConnectedComponent,
        (finiteGraphComponentDimension G localDimension C - 1)) =
      ∑ B : P.parts,
        ((∏ v ∈ B.1, localDimension v) - 1) := by
    apply Fintype.sum_equiv e
    intro C
    rfl
  unfold finiteGraphTemporalRank finpartitionTensorRank
  change
    (∑ C : G.ConnectedComponent,
      (finiteGraphComponentDimension G localDimension C - 1)) =
    ∑ B ∈ P.parts,
      ((∏ v ∈ B, localDimension v) - 1)
  calc
    _ = ∑ B : P.parts,
        ((∏ v ∈ B.1, localDimension v) - 1) := hsum
    _ = ∑ B ∈ P.parts,
        ((∏ v ∈ B, localDimension v) - 1) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach P.parts
        (fun B => ((∏ v ∈ B, localDimension v) - 1))

private theorem bind_restrict_eq_of_le
    {V : Type*} [DecidableEq V] {S : Finset V}
    {P Q : Finpartition S} (hPQ : P ≤ Q) :
    Q.bind (fun _ hB => P.restrict (Q.subset hB)) = P := by
  ext X
  rw [Finpartition.mem_bind]
  constructor
  · rintro ⟨B, hB, hX⟩
    change X ∈ (P.parts.image (· ∩ B)).erase ∅ at hX
    have hXne : X ≠ ∅ := (Finset.mem_erase.mp hX).1
    obtain ⟨A, hA, rfl⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hX).2
    obtain ⟨C, hC, hAC⟩ := hPQ hA
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hXne
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
    have hCB : C = B :=
      Q.eq_of_mem_parts hC hB (hAC hxA) hxB
    have hAB : A ⊆ B := by simpa [hCB] using hAC
    simpa [Finset.inter_eq_left.mpr hAB] using hA
  · intro hX
    obtain ⟨B, hB, hXB⟩ := hPQ hX
    refine ⟨B, hB, ?_⟩
    change X ∈ (P.parts.image (· ∩ B)).erase ∅
    apply Finset.mem_erase.mpr
    constructor
    · exact P.ne_empty hX
    · exact Finset.mem_image.mpr ⟨X, hX,
        Finset.inter_eq_left.mpr hXB⟩

private theorem finpartition_parts_eq_singleton_self_of_card_eq_one
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P : Finpartition S) (hcard : P.parts.card = 1) :
    P.parts = {S} := by
  obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hcard
  have hBS : B = S := by
    have hcover := P.biUnion_parts
    simpa [hparts] using hcover
  simpa [hBS] using hparts

private theorem restrictParts_pairwiseDisjoint
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P Q : Finpartition S) :
    ((Q.parts.attach : Finset Q.parts) : Set Q.parts).PairwiseDisjoint
      (fun B => (P.restrict (Q.subset B.2)).parts) := by
  intro B _ C _ hBC
  change Disjoint
    (P.restrict (Q.subset B.2)).parts
    (P.restrict (Q.subset C.2)).parts
  rw [Finset.disjoint_left]
  intro X hXB hXC
  obtain ⟨x, hxX⟩ :=
    (P.restrict (Q.subset B.2)).nonempty_of_mem_parts hXB
  have hxB : x ∈ B.1 :=
    (P.restrict (Q.subset B.2)).subset hXB hxX
  have hxC : x ∈ C.1 :=
    (P.restrict (Q.subset C.2)).subset hXC hxX
  have hval : B.1 ≠ C.1 := fun h => hBC (Subtype.ext h)
  exact (Finset.disjoint_left.mp
    (Q.disjoint B.2 C.2 hval)) hxB hxC

/-- A refinement rank is the sum of the ranks of its restrictions to the
coarse blocks. -/
theorem finpartitionTensorRank_eq_sum_restrict
    {V : Type*} [DecidableEq V] {S : Finset V}
    (P Q : Finpartition S) (hPQ : P ≤ Q)
    (localDimension : V → ℕ) :
    finpartitionTensorRank P localDimension =
      ∑ B ∈ Q.parts.attach,
        finpartitionTensorRank
          (P.restrict (Q.subset B.2)) localDimension := by
  calc
    finpartitionTensorRank P localDimension =
        finpartitionTensorRank
          (Q.bind (fun B hB => P.restrict (Q.subset hB)))
          localDimension := by
      exact congrArg (fun R => finpartitionTensorRank R localDimension)
        (bind_restrict_eq_of_le hPQ).symm
    _ = ∑ B ∈ Q.parts.attach,
          finpartitionTensorRank
            (P.restrict (Q.subset B.2)) localDimension := by
      unfold finpartitionTensorRank
      rw [Finpartition.bind_parts]
      exact Finset.sum_biUnion
        (f := fun X : Finset V =>
          ((∏ v ∈ X, localDimension v) - 1))
        (restrictParts_pairwiseDisjoint P Q)

/-- Tensor-rank weight is monotone under coarsening of finite
partitions. -/
theorem finpartitionTensorRank_mono
    {V : Type*} [DecidableEq V] {S : Finset V}
    {P Q : Finpartition S} (hPQ : P ≤ Q)
    (localDimension : V → ℕ)
    (hlocal : ∀ v ∈ S, 2 ≤ localDimension v) :
    finpartitionTensorRank P localDimension ≤
      finpartitionTensorRank Q localDimension := by
  rw [finpartitionTensorRank_eq_sum_restrict P Q hPQ]
  unfold finpartitionTensorRank
  rw [← Finset.sum_attach Q.parts
    (fun B => ((∏ v ∈ B, localDimension v) - 1))]
  apply Finset.sum_le_sum
  intro B _
  exact finpartitionTensorRank_le
    (P.restrict (Q.subset B.2)) localDimension
    (fun v hv => hlocal v (Q.subset B.2 hv))

private theorem exists_restrict_card_gt_one_of_lt
    {V : Type*} [DecidableEq V] {S : Finset V}
    {P Q : Finpartition S} (hPQ : P ≤ Q) (hne : P ≠ Q) :
    ∃ B ∈ Q.parts.attach,
      1 < (P.restrict (Q.subset B.2)).parts.card := by
  by_contra hnot
  push Not at hnot
  have hone : ∀ B : Q.parts,
      (P.restrict (Q.subset B.2)).parts = {B.1} := by
    intro B
    have hnonempty :
        (P.restrict (Q.subset B.2)).parts.Nonempty :=
      (P.restrict (Q.subset B.2)).parts_nonempty
        (Q.ne_empty B.2)
    have hcardLower : 1 ≤
        (P.restrict (Q.subset B.2)).parts.card :=
      Finset.one_le_card.mpr hnonempty
    have hcard :
        (P.restrict (Q.subset B.2)).parts.card = 1 := by
      have := hnot B (Finset.mem_attach Q.parts B)
      omega
    exact finpartition_parts_eq_singleton_self_of_card_eq_one
      (P.restrict (Q.subset B.2)) hcard
  have hbind :
      Q.bind (fun B hB => P.restrict (Q.subset hB)) = Q := by
    ext X
    rw [Finpartition.mem_bind]
    constructor
    · rintro ⟨B, hB, hX⟩
      have hs := hone ⟨B, hB⟩
      have hXB : X = B := by simpa [hs] using hX
      simpa [hXB] using hB
    · intro hX
      refine ⟨X, hX, ?_⟩
      have hs := hone ⟨X, hX⟩
      simp [hs]
  exact hne ((bind_restrict_eq_of_le hPQ).symm.trans hbind)

/-- Coarsening is strictly rank-increasing unless the two partitions are
identical. -/
theorem finpartitionTensorRank_strictMono
    {V : Type*} [DecidableEq V] {S : Finset V}
    {P Q : Finpartition S} (hPQ : P ≤ Q) (hne : P ≠ Q)
    (localDimension : V → ℕ)
    (hlocal : ∀ v ∈ S, 2 ≤ localDimension v) :
    finpartitionTensorRank P localDimension <
      finpartitionTensorRank Q localDimension := by
  rw [finpartitionTensorRank_eq_sum_restrict P Q hPQ]
  unfold finpartitionTensorRank
  rw [← Finset.sum_attach Q.parts
    (fun B => ((∏ v ∈ B, localDimension v) - 1))]
  apply Finset.sum_lt_sum
  · intro B _
    exact finpartitionTensorRank_le
      (P.restrict (Q.subset B.2)) localDimension
      (fun v hv => hlocal v (Q.subset B.2 hv))
  · obtain ⟨B, hB, hcard⟩ :=
      exists_restrict_card_gt_one_of_lt hPQ hne
    refine ⟨B, hB, ?_⟩
    exact finpartitionTensorRank_lt_of_one_lt_card
      (P.restrict (Q.subset B.2)) localDimension
      (fun v hv => hlocal v (Q.subset B.2 hv)) hcard

theorem mem_graphConnectedFinpartition_part_iff_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) :
    v ∈ (graphConnectedFinpartition G).part u ↔ G.Reachable u v := by
  classical
  rw [graphConnectedFinpartition,
    Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- Adding graph edges coarsens the connected-component partition. -/
theorem graphConnectedFinpartition_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) :
    graphConnectedFinpartition G ≤
      graphConnectedFinpartition H := by
  classical
  intro B hB
  obtain ⟨v, hv⟩ :=
    (graphConnectedFinpartition G).nonempty_of_mem_parts hB
  refine ⟨(graphConnectedFinpartition H).part v,
    (graphConnectedFinpartition H).part_mem.mpr (Finset.mem_univ v), ?_⟩
  intro w hw
  have hwPart : w ∈ (graphConnectedFinpartition G).part v := by
    rw [(graphConnectedFinpartition G).part_eq_of_mem hB hv]
    exact hw
  apply (mem_graphConnectedFinpartition_part_iff_reachable H v w).mpr
  exact (mem_graphConnectedFinpartition_part_iff_reachable G v w).mp
    hwPart |>.mono hGH

/-- Delete exactly those edges whose endpoints lie in different blocks of
a supplied vertex partition. -/
def finpartitionRestrictedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : Finpartition (Finset.univ : Finset V)) : SimpleGraph V :=
  G ⊓ SimpleGraph.fromRel (fun u v => P.part u = P.part v)

@[simp]
theorem finpartitionRestrictedGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : Finpartition (Finset.univ : Finset V))
    (u v : V) :
    (finpartitionRestrictedGraph G P).Adj u v ↔
      G.Adj u v ∧ P.part u = P.part v := by
  unfold finpartitionRestrictedGraph
  rw [SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, _, hpart | hpart⟩
    · exact ⟨huv, hpart⟩
    · exact ⟨huv, hpart.symm⟩
  · rintro ⟨huv, hpart⟩
    exact ⟨huv, G.ne_of_adj huv, Or.inl hpart⟩

private theorem reachable_finpartitionRestrictedGraph_part_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {P : Finpartition (Finset.univ : Finset V)}
    {u v : V}
    (h : (finpartitionRestrictedGraph G P).Reachable u v) :
    P.part u = P.part v := by
  have hwalk : ∀ {a b : V}
      (p : (finpartitionRestrictedGraph G P).Walk a b),
      P.part a = P.part b := by
    intro a b p
    induction p with
    | nil => rfl
    | cons hadj p ih =>
        exact (finpartitionRestrictedGraph_adj G P _ _).mp hadj |>.2.trans ih
  exact h.elim hwalk

/-- Every connected component left after cross-block edge deletion lies in
one supplied partition block. -/
theorem graphConnectedFinpartition_restricted_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : Finpartition (Finset.univ : Finset V)) :
    graphConnectedFinpartition (finpartitionRestrictedGraph G P) ≤ P := by
  classical
  intro B hB
  obtain ⟨v, hv⟩ :=
    (graphConnectedFinpartition
      (finpartitionRestrictedGraph G P)).nonempty_of_mem_parts hB
  refine ⟨P.part v, P.part_mem.mpr (Finset.mem_univ v), ?_⟩
  intro w hw
  have hwPart : w ∈
      (graphConnectedFinpartition
        (finpartitionRestrictedGraph G P)).part v := by
    rw [(graphConnectedFinpartition
      (finpartitionRestrictedGraph G P)).part_eq_of_mem hB hv]
    exact hw
  have hreach :=
    (mem_graphConnectedFinpartition_part_iff_reachable
      (finpartitionRestrictedGraph G P) v w).mp hwPart
  have hpart := reachable_finpartitionRestrictedGraph_part_eq hreach
  rw [hpart]
  exact P.mem_part_self.mpr (Finset.mem_univ w)

/-- Within one supplied block, cross-block restriction retains exactly the
original induced edges. -/
theorem finpartitionRestrictedGraph_adj_iff_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : Finpartition (Finset.univ : Finset V))
    {B : Finset V} (hB : B ∈ P.parts)
    {u v : V} (hu : u ∈ B) (hv : v ∈ B) :
    (finpartitionRestrictedGraph G P).Adj u v ↔ G.Adj u v := by
  rw [finpartitionRestrictedGraph_adj]
  have hpartu : P.part u = B := P.part_eq_of_mem hB hu
  have hpartv : P.part v = B := P.part_eq_of_mem hB hv
  simp [hpartu, hpartv]

/-- Cross-block deletion preserves the connected-component partition
exactly when no original component is split by the supplied partition. -/
theorem graphConnectedFinpartition_restricted_eq_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (P : Finpartition (Finset.univ : Finset V)) :
    graphConnectedFinpartition (finpartitionRestrictedGraph G P) =
        graphConnectedFinpartition G ↔
      graphConnectedFinpartition G ≤ P := by
  classical
  constructor
  · intro heq
    rw [← heq]
    exact graphConnectedFinpartition_restricted_le G P
  · intro hcomponent
    have hgraph : finpartitionRestrictedGraph G P = G := by
      apply le_antisymm
      · exact inf_le_left
      · intro u v huv
        have hu : u ∈ (graphConnectedFinpartition G).part u :=
          (graphConnectedFinpartition G).mem_part_self.mpr
            (Finset.mem_univ u)
        have hv : v ∈ (graphConnectedFinpartition G).part u :=
          (mem_graphConnectedFinpartition_part_iff_reachable G u v).mpr
            huv.reachable
        obtain ⟨B, hB, hsub⟩ := hcomponent
          ((graphConnectedFinpartition G).part_mem.mpr
            (Finset.mem_univ u))
        have huB := hsub hu
        have hvB := hsub hv
        have hpartu : P.part u = B := P.part_eq_of_mem hB huB
        have hpartv : P.part v = B := P.part_eq_of_mem hB hvB
        exact (finpartitionRestrictedGraph_adj G P u v).mpr
          ⟨huv, hpartu.trans hpartv.symm⟩
    rw [hgraph]

/-- Exact partition curvature: rank lost when all edges crossing supplied
partition blocks are deleted. -/
def finiteGraphPartitionTemporalCurvature
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V)) : ℕ :=
  finiteGraphTemporalRank G localDimension -
    finiteGraphTemporalRank (finpartitionRestrictedGraph G P)
      localDimension

/-- Rank of one supplied block, computed by the connected fragments of the
cross-block-restricted graph.  Inside the block this graph has exactly the
original induced edges. -/
def finiteGraphPartitionBlockTemporalRank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V))
    (B : P.parts) : ℕ :=
  finpartitionTensorRank
    ((graphConnectedFinpartition (finpartitionRestrictedGraph G P)).restrict
      (P.subset B.2)) localDimension

/-- Sum of induced-fragment temporal ranks over every supplied partition
block. -/
def finiteGraphPartitionBlockRankSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V)) : ℕ :=
  ∑ B ∈ P.parts.attach,
    finiteGraphPartitionBlockTemporalRank G localDimension P B

/-- The rank of the graph after cross-block deletion is exactly the sum of
the connected-fragment ranks of all blocks. -/
theorem finiteGraphTemporalRank_restricted_eq_blockRankSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V)) :
    finiteGraphTemporalRank (finpartitionRestrictedGraph G P)
        localDimension =
      finiteGraphPartitionBlockRankSum G localDimension P := by
  rw [finiteGraphTemporalRank_eq_finpartitionTensorRank]
  exact finpartitionTensorRank_eq_sum_restrict
    (graphConnectedFinpartition (finpartitionRestrictedGraph G P))
    P (graphConnectedFinpartition_restricted_le G P) localDimension

/-- Card formula `K_P = τ(V) - Σ_{B∈P}τ(B)` in exact block-fragment
form. -/
theorem finiteGraphPartitionTemporalCurvature_eq_rank_sub_blockRankSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V)) :
    finiteGraphPartitionTemporalCurvature G localDimension P =
      finiteGraphTemporalRank G localDimension -
        finiteGraphPartitionBlockRankSum G localDimension P := by
  unfold finiteGraphPartitionTemporalCurvature
  rw [finiteGraphTemporalRank_restricted_eq_blockRankSum]

/-- Deleting cross-block interactions cannot increase generic temporal
rank. -/
theorem finiteGraphTemporalRank_restricted_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V))
    (hlocal : ∀ v, 2 ≤ localDimension v) :
    finiteGraphTemporalRank (finpartitionRestrictedGraph G P)
        localDimension ≤
      finiteGraphTemporalRank G localDimension := by
  rw [finiteGraphTemporalRank_eq_finpartitionTensorRank,
    finiteGraphTemporalRank_eq_finpartitionTensorRank]
  apply finpartitionTensorRank_mono
    (graphConnectedFinpartition_mono (G :=
      finpartitionRestrictedGraph G P) (H := G) inf_le_left)
  intro v _
  exact hlocal v

/-- Exact non-truncation inequality behind nonnegative partition
curvature. -/
theorem finiteGraphPartitionBlockRankSum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V))
    (hlocal : ∀ v, 2 ≤ localDimension v) :
    finiteGraphPartitionBlockRankSum G localDimension P ≤
      finiteGraphTemporalRank G localDimension := by
  rw [← finiteGraphTemporalRank_restricted_eq_blockRankSum]
  exact finiteGraphTemporalRank_restricted_le
    G localDimension P hlocal

/-- **Exact partition-curvature classifier.** Curvature vanishes exactly
when every original connected component lies in one supplied block. -/
theorem finiteGraphPartitionTemporalCurvature_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (P : Finpartition (Finset.univ : Finset V))
    (hlocal : ∀ v, 2 ≤ localDimension v) :
    finiteGraphPartitionTemporalCurvature G localDimension P = 0 ↔
      graphConnectedFinpartition G ≤ P := by
  let R := graphConnectedFinpartition (finpartitionRestrictedGraph G P)
  let Q := graphConnectedFinpartition G
  have hRQ : R ≤ Q :=
    graphConnectedFinpartition_mono (G :=
      finpartitionRestrictedGraph G P) (H := G) inf_le_left
  have hrank :
      finiteGraphTemporalRank (finpartitionRestrictedGraph G P)
          localDimension ≤
        finiteGraphTemporalRank G localDimension :=
    finiteGraphTemporalRank_restricted_le G localDimension P hlocal
  constructor
  · intro hzero
    have hreverse :
        finiteGraphTemporalRank G localDimension ≤
          finiteGraphTemporalRank (finpartitionRestrictedGraph G P)
            localDimension := by
      exact Nat.sub_eq_zero_iff_le.mp hzero
    have hpart : R = Q := by
      by_contra hne
      have hstrict := finpartitionTensorRank_strictMono
        hRQ hne localDimension (fun v _ => hlocal v)
      rw [← finiteGraphTemporalRank_eq_finpartitionTensorRank,
        ← finiteGraphTemporalRank_eq_finpartitionTensorRank] at hstrict
      exact (not_lt_of_ge hreverse) hstrict
    exact (graphConnectedFinpartition_restricted_eq_iff G P).mp hpart
  · intro hcomponent
    have hpart :=
      (graphConnectedFinpartition_restricted_eq_iff G P).mpr hcomponent
    unfold finiteGraphPartitionTemporalCurvature
    rw [finiteGraphTemporalRank_eq_finpartitionTensorRank,
      finiteGraphTemporalRank_eq_finpartitionTensorRank, hpart,
      Nat.sub_self]

/-- A nonempty finite graph is connected exactly when its component
finpartition has one part. -/
theorem connected_iff_graphConnectedFinpartition_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    G.Connected ↔ (graphConnectedFinpartition G).parts.card = 1 := by
  classical
  constructor
  · intro hG
    let root : V := Classical.arbitrary V
    have hpart : (graphConnectedFinpartition G).part root = Finset.univ := by
      ext v
      rw [mem_graphConnectedFinpartition_part_iff_reachable]
      simp [hG.preconnected root v]
    apply Finset.card_eq_one.mpr
    refine ⟨Finset.univ, ?_⟩
    apply Finset.Subset.antisymm
    · intro B hB
      obtain ⟨v, hv⟩ :=
        (graphConnectedFinpartition G).nonempty_of_mem_parts hB
      have hBpart :=
        (graphConnectedFinpartition G).part_eq_of_mem hB hv
      have hvroot : G.Reachable root v := hG.preconnected root v
      have hpartsame :
          (graphConnectedFinpartition G).part root =
            (graphConnectedFinpartition G).part v := by
        apply (graphConnectedFinpartition G).eq_of_mem_parts
          ((graphConnectedFinpartition G).part_mem.mpr (Finset.mem_univ root))
          ((graphConnectedFinpartition G).part_mem.mpr (Finset.mem_univ v))
          ((graphConnectedFinpartition G).mem_part_self.mpr (Finset.mem_univ root))
        exact (mem_graphConnectedFinpartition_part_iff_reachable G v root).mpr
          hvroot.symm
      have : B = Finset.univ := by
        rw [← hBpart, ← hpartsame, hpart]
      simp [this]
    · intro B hB
      have hBuniv : B = Finset.univ := by simpa using hB
      subst B
      have hm := (graphConnectedFinpartition G).part_mem.mpr
        (Finset.mem_univ root)
      simpa only [hpart] using hm
  · intro hcard
    obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hcard
    have hB : B = Finset.univ := by
      have hcover := (graphConnectedFinpartition G).biUnion_parts
      simpa [hparts] using hcover
    refine ⟨?_⟩
    intro u v
    apply (mem_graphConnectedFinpartition_part_iff_reachable G u v).mp
    have hpartMem :
        (graphConnectedFinpartition G).part u ∈
          (graphConnectedFinpartition G).parts :=
      (graphConnectedFinpartition G).part_mem.mpr (Finset.mem_univ u)
    have hpartEq : (graphConnectedFinpartition G).part u = B := by
      simpa [hparts] using hpartMem
    rw [hpartEq, hB]
    simp

/-- **Connectedness by positive partition curvature.** A nonempty graph is
connected exactly when every partition into at least two blocks has
strictly positive temporal curvature. -/
theorem connected_iff_all_nontrivial_partitionTemporalCurvature_pos
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (localDimension : V → ℕ)
    (hlocal : ∀ v, 2 ≤ localDimension v) :
    G.Connected ↔
      ∀ P : Finpartition (Finset.univ : Finset V),
        1 < P.parts.card →
          0 < finiteGraphPartitionTemporalCurvature
            G localDimension P := by
  constructor
  · intro hG P hP
    have hcomponentCard :
        (graphConnectedFinpartition G).parts.card = 1 :=
      (connected_iff_graphConnectedFinpartition_card_eq_one G).mp hG
    have hnotle : ¬ graphConnectedFinpartition G ≤ P := by
      intro hle
      have hcard := Finpartition.card_mono hle
      omega
    have hne :
        finiteGraphPartitionTemporalCurvature
          G localDimension P ≠ 0 := by
      intro hz
      exact hnotle
        ((finiteGraphPartitionTemporalCurvature_eq_zero_iff
          G localDimension P hlocal).mp hz)
    omega
  · intro hall
    apply (connected_iff_graphConnectedFinpartition_card_eq_one G).mpr
    by_contra hcard
    have hpartsNonempty :
        (graphConnectedFinpartition G).parts.Nonempty :=
      (graphConnectedFinpartition G).parts_nonempty
        Finset.univ_nonempty.ne_empty
    have hpartsOne : 1 ≤
        (graphConnectedFinpartition G).parts.card :=
      Finset.one_le_card.mpr hpartsNonempty
    have hpartsTwo : 1 <
        (graphConnectedFinpartition G).parts.card := by omega
    have hpos := hall (graphConnectedFinpartition G) hpartsTwo
    have hzero :=
      (finiteGraphPartitionTemporalCurvature_eq_zero_iff
        G localDimension (graphConnectedFinpartition G) hlocal).mpr le_rfl
    omega

end

end GaloisForLFunctions.HTGeometry
