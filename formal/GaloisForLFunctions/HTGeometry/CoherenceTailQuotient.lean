import GaloisForLFunctions.HTGeometry.CoherenceEndReconstruction
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Canonical finite-defect coherence quotient

For a locally finite graph, finite vertex changes induce only finite edge defects, so Boolean pair
coherence descends from projective vertex tails to an edge-coherence quotient. The descended map
is injective exactly when every finite-boundary vertex set is finite or cofinite.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

universe u
variable {V : Type u}

theorem edgeBoundary_compl (G : SimpleGraph V) (A : Set V) :
    edgeBoundary G Aᶜ = edgeBoundary G A := by
  ext e
  simp only [edgeBoundary, Set.mem_setOf_eq, Set.mem_compl_iff]
  tauto

theorem edgeBoundary_finite_of_set_finite
    (G : SimpleGraph V) [G.LocallyFinite] {A : Set V} (hA : A.Finite) :
    (edgeBoundary G A).Finite := by
  classical
  let N : Set V := ⋃ v ∈ A, G.neighborSet v
  have hN : N.Finite := hA.biUnion fun v _ => Set.toFinite (G.neighborSet v)
  have hsub : edgeBoundary G A ⊆ (A ×ˢ N) ∪ (N ×ˢ A) := by
    intro e he
    rcases he with ⟨hadj, hcross | hcross⟩
    · left
      refine ⟨hcross.1, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨e.1, hcross.1, hadj⟩
    · right
      refine ⟨?_, hcross.2⟩
      exact Set.mem_iUnion₂.mpr ⟨e.2, hcross.2, hadj.symm⟩
  exact ((hA.prod hN).union (hN.prod hA)).subset hsub

theorem BooleanProjectiveFiniteEquivalent.refl (ε : V → Bool) :
    BooleanProjectiveFiniteEquivalent ε ε := by
  left
  have hset : {v | ε v ≠ ε v} = (∅ : Set V) := by simp
  rw [hset]
  exact Set.finite_empty

theorem BooleanProjectiveFiniteEquivalent.symm {ε δ : V → Bool}
    (h : BooleanProjectiveFiniteEquivalent ε δ) :
    BooleanProjectiveFiniteEquivalent δ ε := by
  rcases h with h | h
  · left
    have hset : {v | δ v ≠ ε v} = {v | ε v ≠ δ v} := by
      ext v
      simp [ne_comm]
    simpa only [hset] using h
  · right
    have hset : {v | δ v = ε v} = {v | ε v = δ v} := by
      ext v
      simp [eq_comm]
    simpa only [hset] using h

theorem BooleanProjectiveFiniteEquivalent.trans {ε δ η : V → Bool}
    (hεδ : BooleanProjectiveFiniteEquivalent ε δ)
    (hδη : BooleanProjectiveFiniteEquivalent δ η) :
    BooleanProjectiveFiniteEquivalent ε η := by
  rcases hεδ with hεδ | hεδ <;> rcases hδη with hδη | hδη
  · left
    apply (hεδ.union hδη).subset
    intro v hv
    simp only [Set.mem_union, Set.mem_setOf_eq] at hv ⊢
    by_cases hpoint : ε v = δ v
    · exact Or.inr fun hδηpoint => hv (hpoint.trans hδηpoint)
    · exact Or.inl hpoint
  · right
    apply (hεδ.union hδη).subset
    intro v hv
    simp only [Set.mem_union, Set.mem_setOf_eq] at hv ⊢
    by_cases hpoint : ε v = δ v
    · exact Or.inr (hpoint.symm.trans hv)
    · exact Or.inl hpoint
  · right
    apply (hεδ.union hδη).subset
    intro v hv
    simp only [Set.mem_union, Set.mem_setOf_eq] at hv ⊢
    by_cases hpoint : δ v = η v
    · exact Or.inl (hv.trans hpoint.symm)
    · exact Or.inr hpoint
  · left
    apply (hεδ.union hδη).subset
    intro v hv
    simp only [Set.mem_union, Set.mem_setOf_eq] at hv ⊢
    by_cases hpoint₁ : ε v = δ v
    · exact Or.inl hpoint₁
    · by_cases hpoint₂ : δ v = η v
      · exact Or.inr hpoint₂
      · exfalso
        apply hv
        cases hε : ε v <;> cases hδ : δ v <;> cases hη : η v <;> simp_all

def booleanProjectiveFiniteSetoid : Setoid (V → Bool) where
  r := BooleanProjectiveFiniteEquivalent
  iseqv := ⟨BooleanProjectiveFiniteEquivalent.refl,
    BooleanProjectiveFiniteEquivalent.symm,
    BooleanProjectiveFiniteEquivalent.trans⟩

theorem BooleanEdgeTailEquivalent.refl (G : SimpleGraph V) (ε : V → Bool) :
    BooleanEdgeTailEquivalent G ε ε := by
  rw [BooleanEdgeTailEquivalent, booleanEdgeDisagreement_eq_edgeBoundary]
  have hset : {v | ε v ≠ ε v} = (∅ : Set V) := by simp
  rw [hset]
  have hboundary : edgeBoundary G (∅ : Set V) = ∅ := by
    ext e
    simp [edgeBoundary]
  rw [hboundary]
  exact Set.finite_empty

theorem BooleanEdgeTailEquivalent.symm {G : SimpleGraph V} {ε δ : V → Bool}
    (h : BooleanEdgeTailEquivalent G ε δ) :
    BooleanEdgeTailEquivalent G δ ε := by
  rw [BooleanEdgeTailEquivalent] at h ⊢
  have hset : booleanEdgeDisagreement G δ ε = booleanEdgeDisagreement G ε δ := by
    ext e
    simp only [booleanEdgeDisagreement, Set.mem_setOf_eq]
    exact and_congr_right fun _ => ne_comm
  simpa only [hset] using h

theorem BooleanEdgeTailEquivalent.trans {G : SimpleGraph V} {ε δ η : V → Bool}
    (hεδ : BooleanEdgeTailEquivalent G ε δ)
    (hδη : BooleanEdgeTailEquivalent G δ η) :
    BooleanEdgeTailEquivalent G ε η := by
  rw [BooleanEdgeTailEquivalent] at hεδ hδη ⊢
  apply (hεδ.union hδη).subset
  intro e he
  rcases he with ⟨hadj, hne⟩
  by_cases hεδpoint : booleanEdgeCoherence ε e = booleanEdgeCoherence δ e
  · right
    exact ⟨hadj, fun hδηpoint => hne (hεδpoint.trans hδηpoint)⟩
  · left
    exact ⟨hadj, hεδpoint⟩

def booleanEdgeTailSetoid (G : SimpleGraph V) : Setoid (V → Bool) where
  r := BooleanEdgeTailEquivalent G
  iseqv := ⟨BooleanEdgeTailEquivalent.refl G,
    BooleanEdgeTailEquivalent.symm,
    BooleanEdgeTailEquivalent.trans⟩

theorem booleanProjectiveFiniteEquivalent_implies_edgeTail
    (G : SimpleGraph V) [G.LocallyFinite] {ε δ : V → Bool}
    (h : BooleanProjectiveFiniteEquivalent ε δ) :
    BooleanEdgeTailEquivalent G ε δ := by
  rw [BooleanEdgeTailEquivalent, booleanEdgeDisagreement_eq_edgeBoundary]
  rcases h with h | h
  · exact edgeBoundary_finite_of_set_finite G h
  · have hcompl : {v | ε v ≠ δ v}ᶜ = {v | ε v = δ v} :=
      complement_disagreementSet ε δ
    have hfinite : ({v | ε v ≠ δ v}ᶜ).Finite := by
      simpa only [hcompl] using h
    rw [← edgeBoundary_compl G {v | ε v ≠ δ v}]
    exact edgeBoundary_finite_of_set_finite G hfinite

/-- Projective Boolean vertex tails modulo finite changes and global complement. -/
def BooleanProjectiveFiniteTail (V : Type u) := Quotient (@booleanProjectiveFiniteSetoid V)

/-- Boolean coherence fields modulo finitely many defective ordered graph edges. -/
def BooleanEdgeCoherenceTail (G : SimpleGraph V) := Quotient (booleanEdgeTailSetoid G)

def booleanProjectiveFiniteTailClass (ε : V → Bool) : BooleanProjectiveFiniteTail V :=
  Quotient.mk _ ε

def booleanEdgeCoherenceTailClass (G : SimpleGraph V) (ε : V → Bool) :
    BooleanEdgeCoherenceTail G :=
  Quotient.mk _ ε

/-- The canonical finite-defect coherence readout from projective vertex tails. -/
def coherenceTailMap (G : SimpleGraph V) [G.LocallyFinite] :
    BooleanProjectiveFiniteTail V → BooleanEdgeCoherenceTail G :=
  Quotient.map id fun _ _ h => booleanProjectiveFiniteEquivalent_implies_edgeTail G h

@[simp] theorem coherenceTailMap_class (G : SimpleGraph V) [G.LocallyFinite]
    (ε : V → Bool) :
    coherenceTailMap G (booleanProjectiveFiniteTailClass ε) =
      booleanEdgeCoherenceTailClass G ε := rfl

/-- Equality of two canonical readouts is exactly finiteness of the domain wall between the two
vertex orientations.  This is the formal kernel formula before any topological presentation by
the end space. -/
theorem coherenceTailMap_class_eq_iff_finite_edgeBoundary
    (G : SimpleGraph V) [G.LocallyFinite] (ε δ : V → Bool) :
    coherenceTailMap G (booleanProjectiveFiniteTailClass ε) =
        coherenceTailMap G (booleanProjectiveFiniteTailClass δ) ↔
      (edgeBoundary G {v | ε v ≠ δ v}).Finite := by
  rw [coherenceTailMap_class, coherenceTailMap_class]
  constructor
  · intro h
    have htail : BooleanEdgeTailEquivalent G ε δ := Quotient.exact h
    rwa [BooleanEdgeTailEquivalent, booleanEdgeDisagreement_eq_edgeBoundary] at htail
  · intro h
    apply Quotient.sound
    change BooleanEdgeTailEquivalent G ε δ
    rwa [BooleanEdgeTailEquivalent, booleanEdgeDisagreement_eq_edgeBoundary]

/-- Kernel at the all-positive orientation: a Boolean phase is invisible to finite-defect edge
coherence exactly when its negative domain has finite edge boundary. -/
theorem coherenceTailMap_eq_allPositive_iff_negativeDomain_finiteBoundary
    (G : SimpleGraph V) [G.LocallyFinite] (ε : V → Bool) :
    coherenceTailMap G (booleanProjectiveFiniteTailClass ε) =
        coherenceTailMap G (booleanProjectiveFiniteTailClass (fun _ => false)) ↔
      (edgeBoundary G {v | ε v = true}).Finite := by
  rw [coherenceTailMap_class_eq_iff_finite_edgeBoundary]
  have hset : {v | ε v ≠ false} = {v | ε v = true} := by
    ext v
    cases ε v <;> simp
  rw [hset]

/-- The canonical coherence readout is injective exactly under the finite-boundary one-ended
condition. -/
theorem coherenceTailMap_injective_iff_finiteBoundaryOneEnded
    (G : SimpleGraph V) [G.LocallyFinite] :
    Function.Injective (coherenceTailMap G) ↔ FiniteBoundaryOneEnded G := by
  constructor
  · intro hinjective
    rw [finiteBoundaryOneEnded_iff_booleanEdgeTail_faithful]
    intro ε δ hedge
    have htarget :
        booleanEdgeCoherenceTailClass G ε = booleanEdgeCoherenceTailClass G δ :=
      Quotient.sound hedge
    have hsource :
        booleanProjectiveFiniteTailClass ε = booleanProjectiveFiniteTailClass δ := by
      apply hinjective
      simpa only [coherenceTailMap_class] using htarget
    exact Quotient.exact hsource
  · intro hG q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro ε δ htarget
    apply Quotient.sound
    apply (finiteBoundaryOneEnded_iff_booleanEdgeTail_faithful G).mp hG ε δ
    exact Quotient.exact htarget

/-- The canonical projective-tail coherence readout on a locally finite Cartesian product of two
infinite preconnected graphs is injective. -/
theorem coherenceTailMap_boxProd_injective
    {W : Type*} [Infinite V] [Infinite W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [(G □ H).LocallyFinite]
    (hG : G.Preconnected) (hH : H.Preconnected) :
    Function.Injective (coherenceTailMap (G □ H)) :=
  (coherenceTailMap_injective_iff_finiteBoundaryOneEnded (G □ H)).mpr
    (finiteBoundaryOneEnded_boxProd G H hG hH)

end GaloisForLFunctions.HTGeometry
