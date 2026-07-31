import GaloisForLFunctions.HTGeometry.CoherenceEnds
import Mathlib.Data.Set.SymmDiff
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

namespace GaloisForLFunctions.HTGeometry

open Set CategoryTheory TopologicalSpace
open scoped symmDiff

variable {V : Type}

/-- The conventional graph end equipped with the inverse-limit topology of discrete
component spaces. -/
def GraphEndSpace (G : SimpleGraph V) := G.end

/-- Components outside a finite deletion carry their discrete topology. -/
noncomputable instance graphComponentComplTopologicalSpace (G : SimpleGraph V)
    (K : (Finset V)ᵒᵖ) : TopologicalSpace (G.componentComplFunctor.obj K) := ⊥

noncomputable instance graphComponentComplDiscreteTopology (G : SimpleGraph V)
    (K : (Finset V)ᵒᵖ) : DiscreteTopology (G.componentComplFunctor.obj K) :=
  ⟨rfl⟩

noncomputable instance graphEndSpaceTopologicalSpace (G : SimpleGraph V) :
    TopologicalSpace (GraphEndSpace G) :=
  TopologicalSpace.induced
    (fun e : GraphEndSpace G => (e : G.end).val)
    Pi.topologicalSpace

theorem continuous_graphEndSpace_val (G : SimpleGraph V) :
    Continuous (fun e : GraphEndSpace G => (e : G.end).val) :=
  continuous_induced_dom

theorem continuous_graphEndSpace_eval (G : SimpleGraph V) (K : (Finset V)ᵒᵖ) :
    Continuous (fun e : GraphEndSpace G => (e : G.end).val K) := by
  exact (continuous_apply K).comp (continuous_graphEndSpace_val G)

theorem isClopen_graphEndSpace_eval_preimage (G : SimpleGraph V)
    (K : (Finset V)ᵒᵖ) (S : Set (G.componentComplFunctor.obj K)) :
    IsClopen {e : GraphEndSpace G | (e : G.end).val K ∈ S} := by
  have hS : IsClopen S := isClopen_discrete S
  exact hS.preimage (continuous_graphEndSpace_eval G K)

theorem isClosed_graphEndSpace_range (G : SimpleGraph V) :
    IsClosed (Set.range (fun e : GraphEndSpace G => (e : G.end).val)) := by
  rw [show Set.range (fun e : GraphEndSpace G => (e : G.end).val) =
      G.componentComplFunctor.sections by
    ext u
    constructor
    · rintro ⟨e, rfl⟩
      exact e.property
    · intro hu
      exact ⟨⟨u, hu⟩, rfl⟩]
  rw [CategoryTheory.Functor.sections]
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro j'
  apply isClosed_iInter
  intro f
  apply isClosed_eq
  · exact continuous_of_discreteTopology.comp (continuous_apply j)
  · exact continuous_apply j'

noncomputable instance graphEndSpaceCompactSpace (G : SimpleGraph V)
    [G.LocallyFinite] [Fact G.Preconnected] : CompactSpace (GraphEndSpace G) := by
  letI (K : (Finset V)ᵒᵖ) : CompactSpace (G.componentComplFunctor.obj K) :=
    Finite.compactSpace
  let f : GraphEndSpace G →
      ((K : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj K) :=
    fun e => (e : G.end).val
  have hf : Topology.IsEmbedding f :=
    ⟨Topology.IsInducing.induced f, fun x y h => by
      apply Subtype.ext
      exact h⟩
  have hclosed : IsClosed (Set.range f) := isClosed_graphEndSpace_range G
  exact (⟨hf, hclosed⟩ : Topology.IsClosedEmbedding f).compactSpace

theorem graphEndSpace_eq_at_of_eq_at_superset (G : SimpleGraph V)
    {K L : Finset V} (hKL : K ⊆ L) {e f : GraphEndSpace G}
    (hL : (e : G.end).val (Opposite.op L) = (f : G.end).val (Opposite.op L)) :
    (e : G.end).val (Opposite.op K) = (f : G.end).val (Opposite.op K) := by
  let h : Opposite.op L ⟶ Opposite.op K := opHomOfLE hKL
  calc
    (e : G.end).val (Opposite.op K) =
        G.componentComplFunctor.map h ((e : G.end).val (Opposite.op L)) :=
      ((e : G.end).property h).symm
    _ = G.componentComplFunctor.map h ((f : G.end).val (Opposite.op L)) :=
      congrArg (G.componentComplFunctor.map h) hL
    _ = (f : G.end).val (Opposite.op K) := (f : G.end).property h

/-- Every open neighborhood in the graph-end inverse limit contains a cylinder determined by
one finite vertex deletion. -/
theorem exists_graphEndSpace_eval_cylinder_subset_of_isOpen (G : SimpleGraph V)
    {U : Set (GraphEndSpace G)} (hU : IsOpen U) {e : GraphEndSpace G} (he : e ∈ U) :
    ∃ K : Finset V,
      {f : GraphEndSpace G |
        (f : G.end).val (Opposite.op K) = (e : G.end).val (Opposite.op K)} ⊆ U := by
  classical
  let valMap : GraphEndSpace G →
      ((K : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj K) :=
    fun x => (x : G.end).val
  have hinducing : Topology.IsInducing valMap := Topology.IsInducing.induced valMap
  obtain ⟨O, hO, hpre⟩ := hinducing.isOpen_iff.mp hU
  have heO : valMap e ∈ O := by
    have : e ∈ valMap ⁻¹' O := by simpa only [hpre] using he
    exact this
  obtain ⟨I, u, hu, hpi⟩ := (isOpen_pi_iff.mp hO) (valMap e) heO
  let L : Finset V := I.biUnion fun K => K.unop
  refine ⟨L, ?_⟩
  intro f hf
  have hfpi : valMap f ∈ (I : Set (Finset V)ᵒᵖ).pi u := by
    intro K hKI
    have hKsubL : K.unop ⊆ L := by
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨K, by simpa using hKI, hv⟩
    have hcoord : valMap f K = valMap e K := by
      exact graphEndSpace_eq_at_of_eq_at_superset G hKsubL hf
    rw [hcoord]
    exact (hu K (by simpa using hKI)).2
  have : valMap f ∈ O := hpi hfpi
  have : f ∈ valMap ⁻¹' O := this
  simpa only [hpre] using this

/-- Every clopen set of graph ends is determined at one finite vertex deletion. -/
theorem exists_graphEndSpace_clopen_eq_eval_preimage (G : SimpleGraph V)
    [G.LocallyFinite] [Fact G.Preconnected]
    (U : Clopens (GraphEndSpace G)) :
    ∃ (K : Finset V) (S : Set (G.ComponentCompl K)),
      (U : Set (GraphEndSpace G)) =
        {e : GraphEndSpace G | (e : G.end).val (Opposite.op K) ∈ S} := by
  classical
  let K : U → Finset V := fun e =>
    Classical.choose
      (exists_graphEndSpace_eval_cylinder_subset_of_isOpen G U.isOpen e.property)
  let C : U → Set (GraphEndSpace G) := fun e =>
    {f | (f : G.end).val (Opposite.op (K e)) =
      ((e.1 : GraphEndSpace G) : G.end).val (Opposite.op (K e))}
  have hCopen : ∀ e, IsOpen (C e) := by
    intro e
    exact (isClopen_graphEndSpace_eval_preimage G (Opposite.op (K e))
      {((e.1 : GraphEndSpace G) : G.end).val (Opposite.op (K e))}).isOpen
  have hCsub : ∀ e, C e ⊆ (U : Set (GraphEndSpace G)) := by
    intro e
    exact Classical.choose_spec
      (exists_graphEndSpace_eval_cylinder_subset_of_isOpen G U.isOpen e.property)
  have hcover : (U : Set (GraphEndSpace G)) ⊆ ⋃ e, C e := by
    intro e he
    apply Set.mem_iUnion.mpr
    refine ⟨⟨e, he⟩, ?_⟩
    rfl
  obtain ⟨t, ht⟩ := U.isClosed.isCompact.elim_finite_subcover C hCopen hcover
  let L : Finset V := t.biUnion K
  let S : Set (G.ComponentCompl L) :=
    ((fun e : GraphEndSpace G => (e : G.end).val (Opposite.op L)) ''
      (U : Set (GraphEndSpace G)))
  refine ⟨L, S, Set.Subset.antisymm ?_ ?_⟩
  · intro e he
    exact ⟨e, he, rfl⟩
  · intro f hf
    rcases hf with ⟨e, heU, hfe⟩
    have hecover : e ∈ ⋃ x ∈ t, C x := ht heU
    simp only [Set.mem_iUnion] at hecover
    rcases hecover with ⟨x, hx⟩
    rcases hx with ⟨hxt, hex⟩
    have hKsubL : K x ⊆ L := by
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨x, hxt, hv⟩
    have hfeK : (f : G.end).val (Opposite.op (K x)) =
        (e : G.end).val (Opposite.op (K x)) :=
      graphEndSpace_eq_at_of_eq_at_superset G hKsubL hfe.symm
    have hfx : f ∈ C x := hfeK.trans hex
    exact hCsub x hfx

theorem edgeBoundary_symmDiff_subset (G : SimpleGraph V) (A B : Set V) :
    edgeBoundary G (A ∆ B) ⊆ edgeBoundary G A ∪ edgeBoundary G B := by
  rintro ⟨v, w⟩ he
  simp only [edgeBoundary, Set.mem_setOf_eq, Set.mem_symmDiff, Set.mem_union] at he ⊢
  rcases he with ⟨hadj, hcross⟩
  by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A <;>
    by_cases hvB : v ∈ B <;> by_cases hwB : w ∈ B <;> simp_all

theorem edgeBoundary_symmDiff_finite (G : SimpleGraph V) {A B : Set V}
    (hA : (edgeBoundary G A).Finite) (hB : (edgeBoundary G B).Finite) :
    (edgeBoundary G (A ∆ B)).Finite :=
  (hA.union hB).subset (edgeBoundary_symmDiff_subset G A B)

theorem edgeBoundary_inter_subset (G : SimpleGraph V) (A B : Set V) :
    edgeBoundary G (A ∩ B) ⊆ edgeBoundary G A ∪ edgeBoundary G B := by
  rintro ⟨v, w⟩ he
  simp only [edgeBoundary, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union] at he ⊢
  rcases he with ⟨hadj, hcross⟩
  by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A <;>
    by_cases hvB : v ∈ B <;> by_cases hwB : w ∈ B <;> simp_all

theorem edgeBoundary_inter_finite (G : SimpleGraph V) {A B : Set V}
    (hA : (edgeBoundary G A).Finite) (hB : (edgeBoundary G B).Finite) :
    (edgeBoundary G (A ∩ B)).Finite :=
  (hA.union hB).subset (edgeBoundary_inter_subset G A B)

@[simp] theorem edgeBoundary_empty (G : SimpleGraph V) :
    edgeBoundary G (∅ : Set V) = ∅ := by
  ext e
  simp [edgeBoundary]

@[simp] theorem edgeBoundary_univ (G : SimpleGraph V) :
    edgeBoundary G (Set.univ : Set V) = ∅ := by
  ext e
  simp [edgeBoundary]

/-- Vertex sets with finite graph boundary. -/
def FiniteBoundarySet (G : SimpleGraph V) :=
  {A : Set V // (edgeBoundary G A).Finite}

/-- The finite support containing every endpoint of a finite graph boundary. -/
noncomputable def finiteBoundarySupport (G : SimpleGraph V) (A : FiniteBoundarySet G) :
    Finset V :=
  (edgeEndpointSupport_finite A.property).toFinset

theorem cutLabel_eq_of_adj_of_not_mem_finiteBoundarySupport
    (G : SimpleGraph V) (A : FiniteBoundarySet G) {v w : V}
    (hv : v ∉ finiteBoundarySupport G A) (hadj : G.Adj v w) :
    cutLabel A.1 v = cutLabel A.1 w := by
  rw [cutLabel_eq_iff]
  constructor
  · intro hvA
    by_contra hwA
    apply hv
    apply (Set.Finite.mem_toFinset (edgeEndpointSupport_finite A.property)).mpr
    apply Or.inl
    exact ⟨(v, w), ⟨hadj, Or.inl ⟨hvA, hwA⟩⟩, rfl⟩
  · intro hwA
    by_contra hvA
    apply hv
    apply (Set.Finite.mem_toFinset (edgeEndpointSupport_finite A.property)).mpr
    apply Or.inl
    exact ⟨(v, w), ⟨hadj, Or.inr ⟨hvA, hwA⟩⟩, rfl⟩

/-- The eventual Boolean label of a finite-boundary set on a component outside all boundary
endpoints. -/
noncomputable def finiteBoundaryComponentLabel (G : SimpleGraph V)
    (A : FiniteBoundarySet G) : G.ComponentCompl (finiteBoundarySupport G A) → Bool :=
  SimpleGraph.ComponentCompl.lift
    (fun {v} (_ : v ∉ finiteBoundarySupport G A) => cutLabel A.1 v)
    (fun {v w} (hv : v ∉ finiteBoundarySupport G A)
      (_ : w ∉ finiteBoundarySupport G A) (hadj : G.Adj v w) =>
      cutLabel_eq_of_adj_of_not_mem_finiteBoundarySupport G A hv hadj)

theorem finiteBoundaryComponentLabel_eq_cutLabel_of_mem
    (G : SimpleGraph V) (A : FiniteBoundarySet G)
    {C : G.ComponentCompl (finiteBoundarySupport G A)} {v : V} (hv : v ∈ C) :
    finiteBoundaryComponentLabel G A C = cutLabel A.1 v := by
  rcases (SimpleGraph.ComponentCompl.mem_supp_iff.mp hv) with ⟨hvK, hC⟩
  subst C
  rfl

/-- A finite-boundary vertex set determines the clopen collection of ends eventually lying in
that set. -/
noncomputable def finiteBoundaryEndClopen (G : SimpleGraph V)
    (A : FiniteBoundarySet G) : Clopens (GraphEndSpace G) where
  carrier := {e | finiteBoundaryComponentLabel G A
    ((e : G.end).val (Opposite.op (finiteBoundarySupport G A))) = true}
  isClopen' := isClopen_graphEndSpace_eval_preimage G
    (Opposite.op (finiteBoundarySupport G A))
    {C | finiteBoundaryComponentLabel G A C = true}

theorem mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
    (G : SimpleGraph V) (A : FiniteBoundarySet G)
    {L : Finset V} (hKL : finiteBoundarySupport G A ⊆ L)
    (e : GraphEndSpace G) {v : V}
    (hv : v ∈ SimpleGraph.ComponentCompl.supp
      ((e : G.end).val (Opposite.op L))) :
    e ∈ finiteBoundaryEndClopen G A ↔ v ∈ A.1 := by
  let h : Opposite.op L ⟶ Opposite.op (finiteBoundarySupport G A) := opHomOfLE hKL
  have hprop := (e : G.end).property h
  change ((e : G.end).val (Opposite.op L)).hom hKL =
    (e : G.end).val (Opposite.op (finiteBoundarySupport G A)) at hprop
  have hvK : v ∈ SimpleGraph.ComponentCompl.supp
      ((e : G.end).val (Opposite.op (finiteBoundarySupport G A))) := by
    rw [← hprop]
    exact SimpleGraph.ComponentCompl.subset_hom _ hKL hv
  change finiteBoundaryComponentLabel G A
      ((e : G.end).val (Opposite.op (finiteBoundarySupport G A))) = true ↔ _
  rw [finiteBoundaryComponentLabel_eq_cutLabel_of_mem G A hvK]
  simp [cutLabel]

/-- Two finite-boundary vertex sets determine the same clopen end sector exactly when they differ
at finitely many vertices. -/
theorem finiteBoundaryEndClopen_eq_iff_symmDiff_finite
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (A B : FiniteBoundarySet G) :
    finiteBoundaryEndClopen G A = finiteBoundaryEndClopen G B ↔
      (A.1 ∆ B.1).Finite := by
  classical
  constructor
  · intro hclopen
    by_contra hnotfinite
    have hDinf : (A.1 ∆ B.1).Infinite := hnotfinite
    let L : Finset V := finiteBoundarySupport G A ∪ finiteBoundarySupport G B
    have hLfinite : ((L : Finset V) : Set V).Finite := L.finite_toSet
    have hTinf : ((A.1 ∆ B.1) \ (L : Set V)).Infinite := hDinf.sdiff hLfinite
    have hTsub : (A.1 ∆ B.1) \ (L : Set V) ⊆ (L : Set V)ᶜ := by
      intro x hx
      exact hx.2
    obtain ⟨C, hCinf, x, hxT, hxcomp⟩ :=
      exists_infinite_component_meeting G L ((A.1 ∆ B.1) \ (L : Set V)) hTinf hTsub
    obtain ⟨e, he⟩ :=
      exists_end_through_infinite_component G (Opposite.op L) C hCinf
    have hxcomponent : x ∈ SimpleGraph.ComponentCompl.supp
        ((e : G.end).val (Opposite.op L)) := by
      exact ⟨hTsub hxT, hxcomp.trans he.symm⟩
    have hAsub : finiteBoundarySupport G A ⊆ L := Finset.subset_union_left
    have hBsub : finiteBoundarySupport G B ⊆ L := Finset.subset_union_right
    have hA := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
      G A hAsub e hxcomponent
    have hB := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
      G B hBsub e hxcomponent
    have hend : e ∈ finiteBoundaryEndClopen G A ↔
        e ∈ finiteBoundaryEndClopen G B := by rw [hclopen]
    have hAB : x ∈ A.1 ↔ x ∈ B.1 := hA.symm.trans (hend.trans hB)
    have hxnot : x ∉ A.1 ∆ B.1 := by
      simp only [Set.mem_symmDiff]
      tauto
    exact hxnot hxT.1
  · intro hfinite
    apply Clopens.ext
    ext e
    let L : Finset V :=
      finiteBoundarySupport G A ∪ finiteBoundarySupport G B ∪ hfinite.toFinset
    have hAsub : finiteBoundarySupport G A ⊆ L := by
      intro v hv
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
    have hBsub : finiteBoundarySupport G B ⊆ L := by
      intro v hv
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv)))
    let C : G.ComponentCompl L := (e : G.end).val (Opposite.op L)
    obtain ⟨v, hvC⟩ := C.nonempty
    have hvnotL : v ∉ L := C.notMem_of_mem hvC
    have hvnotDiff : v ∉ A.1 ∆ B.1 := by
      intro hv
      apply hvnotL
      exact Finset.mem_union.mpr (Or.inr ((Set.Finite.mem_toFinset hfinite).mpr hv))
    have hvAB : v ∈ A.1 ↔ v ∈ B.1 := by
      simp only [Set.mem_symmDiff] at hvnotDiff
      tauto
    have hAmem := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
      G A hAsub e hvC
    have hBmem := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
      G B hBsub e hvC
    exact hAmem.trans (hvAB.trans hBmem.symm)

/-- A vertex set whose membership is invariant along every edge outside one finite set has finite
edge boundary. -/
theorem edgeBoundary_finite_of_adjInvariant_outside_finset
    (G : SimpleGraph V) [G.LocallyFinite] (K : Finset V) (A : Set V)
    (hinvariant : ∀ {v w : V}, v ∉ K → w ∉ K → G.Adj v w →
      (v ∈ A ↔ w ∈ A)) :
    (edgeBoundary G A).Finite := by
  classical
  let N := finiteNeighborSupport G K
  have hN : N.Finite := finiteNeighborSupport_finite G K
  have hK : (K : Set V).Finite := K.finite_toSet
  have hsub : edgeBoundary G A ⊆
      (N ×ˢ (K : Set V)) ∪ ((K : Set V) ×ˢ N) := by
    intro e he
    rcases he with ⟨hadj, hcross⟩
    have hendpoint : e.1 ∈ K ∨ e.2 ∈ K := by
      by_contra hnot
      rw [not_or] at hnot
      have hiff := hinvariant hnot.1 hnot.2 hadj
      rcases hcross with hcross | hcross
      · exact hcross.2 (hiff.mp hcross.1)
      · exact hcross.1 (hiff.mpr hcross.2)
    rcases hendpoint with h₁K | h₂K
    · right
      refine ⟨h₁K, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨e.1, h₁K, hadj⟩
    · left
      refine ⟨?_, h₂K⟩
      exact Set.mem_iUnion₂.mpr ⟨e.2, h₂K, hadj.symm⟩
  exact ((hN.prod hK).union (hK.prod hN)).subset hsub

/-- The union of a selected collection of components outside a finite vertex deletion. -/
def componentSelectionVertexSet (G : SimpleGraph V) (K : Finset V)
    (S : Set (G.ComponentCompl K)) : Set V :=
  {v | ∃ hv : v ∉ K, G.componentComplMk hv ∈ S}

theorem componentSelectionVertexSet_adjInvariant
    (G : SimpleGraph V) (K : Finset V) (S : Set (G.ComponentCompl K))
    {v w : V} (hv : v ∉ K) (hw : w ∉ K) (hadj : G.Adj v w) :
    v ∈ componentSelectionVertexSet G K S ↔
      w ∈ componentSelectionVertexSet G K S := by
  have hcomp := G.componentComplMk_eq_of_adj hv hw hadj
  constructor
  · rintro ⟨_, hvS⟩
    exact ⟨hw, hcomp ▸ hvS⟩
  · rintro ⟨_, hwS⟩
    exact ⟨hv, hcomp.symm ▸ hwS⟩

noncomputable def componentSelectionFiniteBoundarySet
    (G : SimpleGraph V) [G.LocallyFinite] (K : Finset V)
    (S : Set (G.ComponentCompl K)) : FiniteBoundarySet G :=
  ⟨componentSelectionVertexSet G K S,
    edgeBoundary_finite_of_adjInvariant_outside_finset G K _
      (componentSelectionVertexSet_adjInvariant G K S)⟩

theorem mem_componentSelectionVertexSet_iff_of_mem_larger_endComponent
    (G : SimpleGraph V) (K : Finset V) (S : Set (G.ComponentCompl K))
    {L : Finset V} (hKL : K ⊆ L) (e : GraphEndSpace G) {v : V}
    (hv : v ∈ SimpleGraph.ComponentCompl.supp
      ((e : G.end).val (Opposite.op L))) :
    v ∈ componentSelectionVertexSet G K S ↔
      (e : G.end).val (Opposite.op K) ∈ S := by
  rcases (SimpleGraph.ComponentCompl.mem_supp_iff.mp hv) with ⟨hvL, hcompL⟩
  have hvK : v ∉ K := Set.notMem_subset hKL hvL
  let h : Opposite.op L ⟶ Opposite.op K := opHomOfLE hKL
  have hend := G.end_hom_mk_of_mk (e : G.end).property h hvL hcompL.symm
  constructor
  · rintro ⟨_, hvS⟩
    rwa [hend]
  · intro heS
    exact ⟨hvK, hend ▸ heS⟩

theorem finiteBoundaryEndClopen_surjective
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    Function.Surjective (finiteBoundaryEndClopen G) := by
  classical
  intro U
  obtain ⟨K, S, hU⟩ := exists_graphEndSpace_clopen_eq_eval_preimage G U
  let A : FiniteBoundarySet G := componentSelectionFiniteBoundarySet G K S
  refine ⟨A, ?_⟩
  apply Clopens.ext
  ext e
  let L : Finset V := finiteBoundarySupport G A ∪ K
  have hAsub : finiteBoundarySupport G A ⊆ L := Finset.subset_union_left
  have hKsub : K ⊆ L := Finset.subset_union_right
  let C : G.ComponentCompl L := (e : G.end).val (Opposite.op L)
  obtain ⟨v, hvC⟩ := C.nonempty
  have hA := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
    G A hAsub e hvC
  have hS := mem_componentSelectionVertexSet_iff_of_mem_larger_endComponent
    G K S hKsub e hvC
  have hcarrier : e ∈ (U : Set (GraphEndSpace G)) ↔
      (e : G.end).val (Opposite.op K) ∈ S := by
    rw [hU]
    rfl
  exact hA.trans (hS.trans hcarrier.symm)

/-- The Boolean ring of finite-boundary vertex sets, with symmetric difference as addition and
intersection as multiplication. -/
def finiteBoundarySubring (G : SimpleGraph V) : Subring (AsBoolRing (Set V)) where
  carrier := {A | (edgeBoundary G (ofBoolRing A)).Finite}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro A B hA hB
    simpa only [ofBoolRing_add] using! edgeBoundary_symmDiff_finite G hA hB
  mul_mem' := by
    intro A B hA hB
    simpa only [ofBoolRing_mul] using! edgeBoundary_inter_finite G hA hB
  neg_mem' := by
    intro A hA
    simpa only [ofBoolRing_neg] using! hA

/-- The ideal of finite vertex sets inside the finite-boundary Boolean ring. -/
def finiteVertexSetIdeal (G : SimpleGraph V) : Ideal (finiteBoundarySubring G) where
  carrier := {A | (ofBoolRing A.1).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    simpa only [Subring.coe_add, ofBoolRing_add] using! hA.symmDiff hB
  smul_mem' := by
    intro A B hB
    simpa only [smul_eq_mul, Subring.coe_mul, ofBoolRing_mul] using!
      hB.inter_of_right (ofBoolRing A.1)

def finiteBoundaryEmpty (G : SimpleGraph V) : FiniteBoundarySet G :=
  ⟨∅, by simp⟩

def finiteBoundaryUniv (G : SimpleGraph V) : FiniteBoundarySet G :=
  ⟨Set.univ, by simp⟩

def finiteBoundarySymmDiff (G : SimpleGraph V) (A B : FiniteBoundarySet G) :
    FiniteBoundarySet G :=
  ⟨A.1 ∆ B.1, edgeBoundary_symmDiff_finite G A.2 B.2⟩

def finiteBoundaryInter (G : SimpleGraph V) (A B : FiniteBoundarySet G) :
    FiniteBoundarySet G :=
  ⟨A.1 ∩ B.1, edgeBoundary_inter_finite G A.2 B.2⟩

theorem finiteBoundaryEndClopen_empty
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    finiteBoundaryEndClopen G (finiteBoundaryEmpty G) = ⊥ := by
  apply Clopens.ext
  ext e
  let K := finiteBoundarySupport G (finiteBoundaryEmpty G)
  let C : G.ComponentCompl K := (e : G.end).val (Opposite.op K)
  obtain ⟨v, hvC⟩ := C.nonempty
  have hmem := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
    G (finiteBoundaryEmpty G) (by exact Finset.Subset.rfl) e hvC
  change e ∈ finiteBoundaryEndClopen G (finiteBoundaryEmpty G) ↔ False
  exact hmem.trans (by simp [finiteBoundaryEmpty])

theorem finiteBoundaryEndClopen_univ
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    finiteBoundaryEndClopen G (finiteBoundaryUniv G) = ⊤ := by
  apply Clopens.ext
  ext e
  let K := finiteBoundarySupport G (finiteBoundaryUniv G)
  let C : G.ComponentCompl K := (e : G.end).val (Opposite.op K)
  obtain ⟨v, hvC⟩ := C.nonempty
  have hmem := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
    G (finiteBoundaryUniv G) (by exact Finset.Subset.rfl) e hvC
  change e ∈ finiteBoundaryEndClopen G (finiteBoundaryUniv G) ↔ True
  exact hmem.trans (by simp [finiteBoundaryUniv])

theorem finiteBoundaryEndClopen_symmDiff
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (A B : FiniteBoundarySet G) :
    finiteBoundaryEndClopen G (finiteBoundarySymmDiff G A B) =
      finiteBoundaryEndClopen G A ∆ finiteBoundaryEndClopen G B := by
  classical
  apply Clopens.ext
  ext e
  let L : Finset V := finiteBoundarySupport G (finiteBoundarySymmDiff G A B) ∪
    finiteBoundarySupport G A ∪ finiteBoundarySupport G B
  have hABsub : finiteBoundarySupport G (finiteBoundarySymmDiff G A B) ⊆ L := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  have hAsub : finiteBoundarySupport G A ⊆ L := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv)))
  have hBsub : finiteBoundarySupport G B ⊆ L := Finset.subset_union_right
  let C : G.ComponentCompl L := (e : G.end).val (Opposite.op L)
  obtain ⟨v, hvC⟩ := C.nonempty
  have hAB := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
    G (finiteBoundarySymmDiff G A B) hABsub e hvC
  have hA := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component G A hAsub e hvC
  have hB := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component G B hBsub e hvC
  change e ∈ finiteBoundaryEndClopen G (finiteBoundarySymmDiff G A B) ↔
    (e ∈ finiteBoundaryEndClopen G A ∧ e ∉ finiteBoundaryEndClopen G B) ∨
    (e ∈ finiteBoundaryEndClopen G B ∧ e ∉ finiteBoundaryEndClopen G A)
  rw [hAB, hA, hB]
  rfl

theorem finiteBoundaryEndClopen_inter
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (A B : FiniteBoundarySet G) :
    finiteBoundaryEndClopen G (finiteBoundaryInter G A B) =
      finiteBoundaryEndClopen G A ⊓ finiteBoundaryEndClopen G B := by
  classical
  apply Clopens.ext
  ext e
  let L : Finset V := finiteBoundarySupport G (finiteBoundaryInter G A B) ∪
    finiteBoundarySupport G A ∪ finiteBoundarySupport G B
  have hABsub : finiteBoundarySupport G (finiteBoundaryInter G A B) ⊆ L := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  have hAsub : finiteBoundarySupport G A ⊆ L := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv)))
  have hBsub : finiteBoundarySupport G B ⊆ L := Finset.subset_union_right
  let C : G.ComponentCompl L := (e : G.end).val (Opposite.op L)
  obtain ⟨v, hvC⟩ := C.nonempty
  have hAB := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component
    G (finiteBoundaryInter G A B) hABsub e hvC
  have hA := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component G A hAsub e hvC
  have hB := mem_finiteBoundaryEndClopen_iff_of_mem_larger_component G B hBsub e hvC
  change e ∈ finiteBoundaryEndClopen G (finiteBoundaryInter G A B) ↔
    e ∈ finiteBoundaryEndClopen G A ∧ e ∈ finiteBoundaryEndClopen G B
  rw [hAB, hA, hB]
  rfl

def finiteBoundarySetOfSubring (G : SimpleGraph V) (A : finiteBoundarySubring G) :
    FiniteBoundarySet G :=
  ⟨ofBoolRing A.1, A.2⟩

@[simp] theorem finiteBoundarySetOfSubring_zero (G : SimpleGraph V) :
    finiteBoundarySetOfSubring G 0 = finiteBoundaryEmpty G := by
  apply Subtype.ext
  rfl

@[simp] theorem finiteBoundarySetOfSubring_one (G : SimpleGraph V) :
    finiteBoundarySetOfSubring G 1 = finiteBoundaryUniv G := by
  apply Subtype.ext
  rfl

@[simp] theorem finiteBoundarySetOfSubring_add (G : SimpleGraph V)
    (A B : finiteBoundarySubring G) :
    finiteBoundarySetOfSubring G (A + B) =
      finiteBoundarySymmDiff G (finiteBoundarySetOfSubring G A)
        (finiteBoundarySetOfSubring G B) := by
  apply Subtype.ext
  rfl

@[simp] theorem finiteBoundarySetOfSubring_mul (G : SimpleGraph V)
    (A B : finiteBoundarySubring G) :
    finiteBoundarySetOfSubring G (A * B) =
      finiteBoundaryInter G (finiteBoundarySetOfSubring G A)
        (finiteBoundarySetOfSubring G B) := by
  apply Subtype.ext
  rfl

/-- The Boolean-ring readout from finite-boundary vertex sets to clopen end sectors. -/
noncomputable def finiteBoundaryEndRingHom
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    finiteBoundarySubring G →+* AsBoolRing (Clopens (GraphEndSpace G)) where
  toFun A := toBoolRing (finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G A))
  map_zero' := by
    change finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G 0) = ⊥
    rw [finiteBoundarySetOfSubring_zero, finiteBoundaryEndClopen_empty]
  map_one' := by
    change finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G 1) = ⊤
    rw [finiteBoundarySetOfSubring_one, finiteBoundaryEndClopen_univ]
  map_add' A B := by
    change finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G (A + B)) =
      finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G A) ∆
        finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G B)
    rw [finiteBoundarySetOfSubring_add, finiteBoundaryEndClopen_symmDiff]
  map_mul' A B := by
    change finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G (A * B)) =
      finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G A) ⊓
        finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G B)
    rw [finiteBoundarySetOfSubring_mul, finiteBoundaryEndClopen_inter]

theorem finiteBoundaryEndRingHom_surjective
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    Function.Surjective (finiteBoundaryEndRingHom G) := by
  intro U
  obtain ⟨A, hA⟩ := finiteBoundaryEndClopen_surjective G (ofBoolRing U)
  let A' : finiteBoundarySubring G := ⟨toBoolRing A.1, A.2⟩
  refine ⟨A', ?_⟩
  change toBoolRing (finiteBoundaryEndClopen G A) = U
  rw [hA]
  exact toBoolRing_ofBoolRing U

theorem mem_finiteBoundaryEndRingHom_ker_iff_finite
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (A : finiteBoundarySubring G) :
    A ∈ RingHom.ker (finiteBoundaryEndRingHom G) ↔ (ofBoolRing A.1).Finite := by
  rw [RingHom.mem_ker]
  change finiteBoundaryEndClopen G (finiteBoundarySetOfSubring G A) = ⊥ ↔ _
  rw [← finiteBoundaryEndClopen_empty G,
    finiteBoundaryEndClopen_eq_iff_symmDiff_finite]
  change ((ofBoolRing A.1 : Set V) ∆ ∅).Finite ↔ (ofBoolRing A.1).Finite
  have h : (ofBoolRing A.1 : Set V) ∆ ∅ = ofBoolRing A.1 := by
    ext v
    simp [Set.mem_symmDiff]
  rw [h]

theorem finiteBoundaryEndRingHom_ker
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    RingHom.ker (finiteBoundaryEndRingHom G) = finiteVertexSetIdeal G := by
  ext A
  exact mem_finiteBoundaryEndRingHom_ker_iff_finite G A

/-- **Finite-boundary/clopen-end Boolean algebra presentation.** For an infinite locally finite
connected graph, finite-boundary vertex sets modulo finite symmetric difference are isomorphic,
as a Boolean ring, to the clopen subsets of the conventional graph-end space. -/
noncomputable def finiteBoundaryBooleanRingQuotientEquivClopens
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    (finiteBoundarySubring G ⧸ finiteVertexSetIdeal G) ≃+*
      AsBoolRing (Clopens (GraphEndSpace G)) :=
  (Ideal.quotEquivOfEq (finiteBoundaryEndRingHom_ker G).symm).trans
    ((finiteBoundaryEndRingHom G).quotientKerEquivOfSurjective
      (finiteBoundaryEndRingHom_surjective G))

end GaloisForLFunctions.HTGeometry
