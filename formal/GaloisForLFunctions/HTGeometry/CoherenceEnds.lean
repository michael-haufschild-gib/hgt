import GaloisForLFunctions.HTGeometry.CoherenceEndReconstruction
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Conventional graph ends from finite-boundary coherence

For infinite locally finite preconnected graphs, the finite-boundary coherence condition is
exactly equivalent to the conventional inverse-system end type being subsingleton. The proof
constructs ends through arbitrary infinite complement components and uses finite pigeonhole
control of components after a finite edge defect.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open CategoryTheory

variable {V : Type}

/-- Neighbor support of a finite vertex set. -/
def finiteNeighborSupport (G : SimpleGraph V) (K : Finset V) : Set V :=
  ⋃ k ∈ K, G.neighborSet k

theorem finiteNeighborSupport_finite (G : SimpleGraph V) [G.LocallyFinite]
    (K : Finset V) : (finiteNeighborSupport G K).Finite := by
  classical
  exact K.finite_toSet.biUnion fun k _ => Set.toFinite (G.neighborSet k)

/-- A component outside a finite vertex set has finite ordered edge boundary in a locally finite
graph. -/
theorem edgeBoundary_componentCompl_finite
    (G : SimpleGraph V) [G.LocallyFinite] (K : Finset V)
    (C : G.ComponentCompl K) :
    (edgeBoundary G (C : Set V)).Finite := by
  classical
  let N := finiteNeighborSupport G K
  have hN : N.Finite := finiteNeighborSupport_finite G K
  have hK : (K : Set V).Finite := K.finite_toSet
  have hsub : edgeBoundary G (C : Set V) ⊆
      (N ×ˢ (K : Set V)) ∪ ((K : Set V) ×ˢ N) := by
    intro e he
    rcases he with ⟨hadj, hcross | hcross⟩
    · have he₂K : e.2 ∈ K := by
        by_contra he₂K
        exact hcross.2 (C.mem_of_adj e.1 e.2 hcross.1 he₂K hadj)
      left
      refine ⟨?_, he₂K⟩
      exact Set.mem_iUnion₂.mpr ⟨e.2, he₂K, hadj.symm⟩
    · have he₁K : e.1 ∈ K := by
        by_contra he₁K
        exact hcross.1 (C.mem_of_adj e.2 e.1 hcross.2 he₁K hadj.symm)
      right
      refine ⟨he₁K, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨e.1, he₁K, hadj⟩
  exact ((hN.prod hK).union (hK.prod hN)).subset hsub

/-- The formal finite-boundary one-ended condition forces the conventional inverse-system end
type to have at most one element. -/
theorem subsingleton_end_of_finiteBoundaryOneEnded
    (G : SimpleGraph V) [G.LocallyFinite]
    (hG : FiniteBoundaryOneEnded G) :
    Subsingleton G.end := by
  constructor
  intro e₁ e₂
  apply Subtype.ext
  funext K
  by_contra hne
  let C₁ : G.ComponentCompl K.unop := e₁.val K
  let C₂ : G.ComponentCompl K.unop := e₂.val K
  have hC₁neC₂ : C₁ ≠ C₂ := by
    simpa only [C₁, C₂] using! hne
  have hC₁inf : (C₁ : Set V).Infinite := by
    simpa only [C₁] using! SimpleGraph.end_componentCompl_infinite G e₁ K
  have hC₂inf : (C₂ : Set V).Infinite := by
    simpa only [C₂] using! SimpleGraph.end_componentCompl_infinite G e₂ K
  have hdisjoint : Disjoint (C₁ : Set V) (C₂ : Set V) :=
    SimpleGraph.ComponentCompl.pairwise_disjoint hC₁neC₂
  have hC₂sub : (C₂ : Set V) ⊆ (C₁ : Set V)ᶜ := by
    intro x hx₂
    simp only [Set.mem_compl_iff]
    intro hx₁
    exact Set.disjoint_left.mp hdisjoint hx₁ hx₂
  rcases hG (C₁ : Set V) (edgeBoundary_componentCompl_finite G K.unop C₁) with
      hC₁finite | hC₁cofinite
  · exact hC₁inf hC₁finite
  · exact hC₂inf (hC₁cofinite.subset hC₂sub)

/-- Every infinite component outside a finite vertex set is the value of some conventional graph
end at that finite set. -/
theorem exists_end_through_infinite_component
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (K : (Finset V)ᵒᵖ) (C : G.componentComplFunctor.obj K)
    (hC : C.supp.Infinite) :
    ∃ e : G.end, e.val K = C := by
  classical
  let F := G.componentComplFunctor
  have hML : F.IsMittagLeffler := by
    apply F.isMittagLeffler_of_exists_finite_range
    intro j
    refine ⟨j, 𝟙 j, ?_⟩
    exact Set.toFinite (Set.range (F.map (𝟙 j)))
  letI : ∀ j, Nonempty (F.toEventualRanges.obj j) :=
    fun j => F.toEventualRanges_nonempty hML j
  have hsurj : ∀ ⦃i j⦄ (f : i ⟶ j),
      Function.Surjective (F.toEventualRanges.map f) :=
    fun _ _ f =>
      CategoryTheory.Functor.surjective_toEventualRanges F hML f
  have hCeventual : C ∈ F.eventualRange K :=
    (SimpleGraph.infinite_iff_in_eventualRange G C).mp hC
  let C' : F.toEventualRanges.obj K := ⟨C, hCeventual⟩
  obtain ⟨sec, hsec⟩ :=
    F.toEventualRanges.eval_section_surjective_of_surjective hsurj K C'
  let e : G.end := F.toEventualRangesSectionsEquiv sec
  refine ⟨e, ?_⟩
  exact congrArg Subtype.val hsec

/-- An infinite vertex set disjoint from a finite deletion set meets some infinite component of
the deleted graph. -/
theorem exists_infinite_component_meeting
    (G : SimpleGraph V) [G.LocallyFinite] [Fact G.Preconnected]
    (K : Finset V) (T : Set V) (hT : T.Infinite) (hTK : T ⊆ (K : Set V)ᶜ) :
    ∃ C : G.ComponentCompl K,
      (C : Set V).Infinite ∧ ∃ x, ∃ hx : x ∈ T, G.componentComplMk (hTK hx) = C := by
  classical
  let comp : T → G.ComponentCompl K := fun x => G.componentComplMk (hTK x.2)
  letI : Infinite T := hT.to_subtype
  obtain ⟨C, hCfiber⟩ := Finite.exists_infinite_fiber comp
  let X := comp ⁻¹' ({C} : Set (G.ComponentCompl K))
  letI : Infinite X := hCfiber
  have hCinf : (C : Set V).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun x : X => (x.1.1 : V))
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
    · intro x
      have hxcomp : comp x.1 = C := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using! x.2
      rw [← hxcomp]
      exact G.componentComplMk_mem (hTK x.1.2)
  refine ⟨C, hCinf, ?_⟩
  haveI : Nonempty X := Infinite.nonempty X
  let x : X := Classical.choice ‹Nonempty X›
  refine ⟨x.1.1, x.1.2, ?_⟩
  change comp x.1 = C
  simpa only [X, Set.mem_preimage, Set.mem_singleton_iff] using x.2

/-- For an infinite locally finite preconnected graph, a subsingleton conventional end type
forces every finite-edge-boundary vertex set to be finite or cofinite. -/
theorem finiteBoundaryOneEnded_of_subsingleton_end
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (hEnd : Subsingleton G.end) :
    FiniteBoundaryOneEnded G := by
  intro A hboundary
  classical
  by_contra hnot
  rw [not_or] at hnot
  have hAinf : A.Infinite := hnot.1
  have hAcinf : Aᶜ.Infinite := hnot.2
  let F : Set (V × V) := edgeBoundary G A
  let S : Set V := edgeEndpointSupport F
  have hS : S.Finite := by
    dsimp [S, F]
    exact edgeEndpointSupport_finite hboundary
  let K : Finset V := hS.toFinset
  have hK : (K : Set V).Finite := K.finite_toSet
  have hinvariant : ∀ ⦃v w : V⦄ (hv : v ∉ (K : Set V)) (hw : w ∉ (K : Set V)),
      G.Adj v w → cutLabel A v = cutLabel A w := by
    intro v w hv hw hadj
    rw [cutLabel_eq_iff]
    constructor
    · intro hvA
      by_contra hwA
      apply hv
      have hedge : (v, w) ∈ F := by
        exact ⟨hadj, Or.inl ⟨hvA, hwA⟩⟩
      have hvS : v ∈ S := by
        apply Or.inl
        exact ⟨(v, w), hedge, rfl⟩
      change v ∈ hS.toFinset
      exact (Set.Finite.mem_toFinset hS).mpr hvS
    · intro hwA
      by_contra hvA
      apply hv
      have hedge : (v, w) ∈ F := by
        exact ⟨hadj, Or.inr ⟨hvA, hwA⟩⟩
      have hvS : v ∈ S := by
        apply Or.inl
        exact ⟨(v, w), hedge, rfl⟩
      change v ∈ hS.toFinset
      exact (Set.Finite.mem_toFinset hS).mpr hvS
  let label : G.ComponentCompl K → Bool :=
    SimpleGraph.ComponentCompl.lift
      (fun {v} (_ : v ∉ (K : Set V)) => cutLabel A v)
      (fun {v w} hv hw hadj => hinvariant hv hw hadj)
  have hTAinf : (A \ (K : Set V)).Infinite := hAinf.diff hK
  have hTAK : A \ (K : Set V) ⊆ (K : Set V)ᶜ := by
    intro x hx
    exact hx.2
  obtain ⟨C_A, hC_Ainf, x_A, hx_A, hx_Acomp⟩ :=
    exists_infinite_component_meeting G K (A \ (K : Set V)) hTAinf hTAK
  have hTcinf : (Aᶜ \ (K : Set V)).Infinite := hAcinf.diff hK
  have hTcK : Aᶜ \ (K : Set V) ⊆ (K : Set V)ᶜ := by
    intro x hx
    exact hx.2
  obtain ⟨C_c, hC_cinf, x_c, hx_c, hx_ccomp⟩ :=
    exists_infinite_component_meeting G K (Aᶜ \ (K : Set V)) hTcinf hTcK
  have hlabelA : label C_A = true := by
    rw [← hx_Acomp]
    change cutLabel A x_A = true
    simp [cutLabel, hx_A.1]
  have hlabelc : label C_c = false := by
    rw [← hx_ccomp]
    change cutLabel A x_c = false
    have hxcnot : x_c ∉ A := hx_c.1
    simp [cutLabel, hxcnot]
  have hCne : C_A ≠ C_c := by
    intro hC
    rw [hC] at hlabelA
    rw [hlabelc] at hlabelA
    contradiction
  obtain ⟨e_A, he_A⟩ :=
    exists_end_through_infinite_component G (Opposite.op K) C_A hC_Ainf
  obtain ⟨e_c, he_c⟩ :=
    exists_end_through_infinite_component G (Opposite.op K) C_c hC_cinf
  have heqEnds : e_A = e_c := @Subsingleton.elim G.end hEnd e_A e_c
  apply hCne
  rw [← he_A, ← he_c]
  exact congrArg (fun e : G.end => e.val (Opposite.op K)) heqEnds

/-- **End/coherence equivalence.**  On an infinite locally finite preconnected graph, the exact
finite-boundary coherence condition is equivalent to the conventional graph end type having one
element up to subsingleton equality. -/
theorem finiteBoundaryOneEnded_iff_subsingleton_end
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected] :
    FiniteBoundaryOneEnded G ↔ Subsingleton G.end := by
  constructor
  · exact subsingleton_end_of_finiteBoundaryOneEnded G
  · exact finiteBoundaryOneEnded_of_subsingleton_end G

end GaloisForLFunctions.HTGeometry
