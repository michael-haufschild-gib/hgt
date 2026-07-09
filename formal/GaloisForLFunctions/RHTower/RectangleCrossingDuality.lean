/-
# Rectangle crossing duality (planar topology infrastructure)

A rectangle can be crossed in exactly one of two dual ways.  Mathlib has no Brouwer fixed point,
no Jordan curve theorem, and no discrete Steinhaus/Hex duality; this file builds the crossing
duality that planar function theory needs, in three stages.

* **Stage A** (`compact_separation_of_no_joining_component`).  Compact clopen separation.  If no
  connected subset of a compact set `K` in a Hausdorff space meets both closed sets `A` and `B`,
  then `K` splits into two disjoint compacts, one missing `A`, the other missing `B`.  The pieces
  are relatively clopen in `K`.  The per-point engine (a clopen neighbourhood of `x` avoiding a
  compact set that misses the connected component of `x`) is
  `Bottcher.exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent`; Stage A
  is the finite-cover Boolean assembly on top of it.

* **Stage B** (`discrete_crossing_duality`).  The discrete Hex/Steinhaus duality on a grid board:
  either the marked cells contain a king-connected chain from the bottom row to the top row, or the
  free cells contain a rook-connected chain from the left column to the right column.

* **Stage C** (`rectangle_crossing_duality`).  Either `K` contains a connected curtain inside the
  closed rectangle joining bottom edge to top edge, or the complement contains a polygonal path from
  the left edge to the right edge.
-/
import Mathlib
import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance

open Set

namespace RHTower

/-- **Stage A — compact clopen separation.**  Work in the compact Hausdorff subspace `K`.  For each
`x ∈ K` the connected component of `x` misses `A` or misses `B` (its image is a connected subset of
`K`, so the hypothesis forbids it from meeting both).  Because the space is compact Hausdorff, a
connected component is the intersection of its clopen neighbourhoods, so a single clopen neighbourhood
of `x` already avoids whichever of `A`, `B` the component misses.  Cover `K` by these clopens, take a
finite subcover, and let `K₁` be the union of the members avoiding `B`; its complement in `K` avoids
`A`.  Push both relatively-clopen pieces back to `X` as compact sets. -/
theorem compact_separation_of_no_joining_component {X : Type*} [TopologicalSpace X] [T2Space X]
    {K A B : Set X} (hK : IsCompact K) (hA : IsClosed A) (hB : IsClosed B)
    (h : ∀ C ⊆ K, IsConnected C → ¬((C ∩ A).Nonempty ∧ (C ∩ B).Nonempty)) :
    ∃ K₁ K₂ : Set X, K = K₁ ∪ K₂ ∧ IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧
      K₁ ∩ B = ∅ ∧ K₂ ∩ A = ∅ := by
  classical
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  set A' : Set ↥K := Subtype.val ⁻¹' A with hA'def
  set B' : Set ↥K := Subtype.val ⁻¹' B with hB'def
  have hA'cpt : IsCompact A' := (hA.preimage continuous_subtype_val).isCompact
  have hB'cpt : IsCompact B' := (hB.preimage continuous_subtype_val).isCompact
  -- Each component misses `A` or misses `B`.
  have hcomp_ab : ∀ x : ↥K,
      Disjoint A' (connectedComponent x) ∨ Disjoint B' (connectedComponent x) := by
    intro x
    have hc : IsConnected (Subtype.val '' connectedComponent x) :=
      (isConnected_connectedComponent).image _ continuous_subtype_val.continuousOn
    have hsub : Subtype.val '' connectedComponent x ⊆ K := by
      rintro y ⟨c, _, rfl⟩; exact c.2
    rcases not_and_or.mp (h _ hsub hc) with hA0 | hB0
    · left
      rw [Set.disjoint_left]
      intro p hpA' hpComp
      exact hA0 ⟨(p : X), ⟨p, hpComp, rfl⟩, hpA'⟩
    · right
      rw [Set.disjoint_left]
      intro p hpB' hpComp
      exact hB0 ⟨(p : X), ⟨p, hpComp, rfl⟩, hpB'⟩
  -- Per-point clopen neighbourhood, tagged by which set it avoids.
  have key : ∀ x : ↥K, ∃ E : Set ↥K, IsClopen E ∧ x ∈ E ∧
      (Disjoint B' E ∨ Disjoint A' E) := by
    intro x
    rcases hcomp_ab x with hDA | hDB
    · obtain ⟨E, hEcl, hExmem, hEdisj⟩ :=
        Bottcher.exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent
          hA'cpt hDA
      exact ⟨E, hEcl, hExmem, Or.inr hEdisj⟩
    · obtain ⟨E, hEcl, hExmem, hEdisj⟩ :=
        Bottcher.exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent
          hB'cpt hDB
      exact ⟨E, hEcl, hExmem, Or.inl hEdisj⟩
  choose E hEcl hExmem hEdisj using key
  -- Finite subcover of the compact space.
  have hcover : (univ : Set ↥K) ⊆ ⋃ x, E x := fun x _ => mem_iUnion.2 ⟨x, hExmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover E (fun x => (hEcl x).isOpen) hcover
  -- `S₁` = union of the pieces avoiding `B`; `S₂` = its complement.
  set S₁ : Set ↥K := ⋃ x ∈ t.filter (fun x => Disjoint B' (E x)), E x with hS1def
  have hS1cl : IsClopen S₁ := isClopen_biUnion_finset (fun x _ => hEcl x)
  set S₂ : Set ↥K := S₁ᶜ with hS2def
  have hS2cl : IsClopen S₂ := hS1cl.compl
  have hunion : S₁ ∪ S₂ = univ := Set.union_compl_self S₁
  have hdisjS : Disjoint S₁ S₂ := disjoint_compl_right
  -- `S₁` avoids `B`.
  have hB'S1 : Disjoint B' S₁ := by
    rw [hS1def, Set.disjoint_iUnion₂_right]
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  -- `S₂` avoids `A`.
  have hA'S2 : Disjoint A' S₂ := by
    rw [Set.disjoint_left]
    intro p hpA' hpS2
    have hpcov : p ∈ ⋃ x ∈ t, E x := ht (mem_univ p)
    rw [mem_iUnion₂] at hpcov
    obtain ⟨x, hxt, hpEx⟩ := hpcov
    rcases hEdisj x with hDB | hDA
    · -- then `x` is in the filtered set, so `p ∈ S₁`, contradicting `p ∈ S₂`.
      have : p ∈ S₁ := by
        rw [hS1def]
        exact mem_iUnion₂.2 ⟨x, Finset.mem_filter.mpr ⟨hxt, hDB⟩, hpEx⟩
      exact hpS2 this
    · exact (Set.disjoint_left.mp hDA) hpA' hpEx
  -- Push the two relatively-clopen pieces back to `X`.
  refine ⟨Subtype.val '' S₁, Subtype.val '' S₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Set.image_union, hunion, Subtype.coe_image_univ]
  · exact (hS1cl.isClosed.isCompact).image continuous_subtype_val
  · exact (hS2cl.isClosed.isCompact).image continuous_subtype_val
  · exact (Set.disjoint_image_iff Subtype.val_injective).mpr hdisjS
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨p, hpS1, rfl⟩, hyB⟩
    exact (Set.disjoint_left.mp hB'S1) hyB hpS1
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨p, hpS2, rfl⟩, hyA⟩
    exact (Set.disjoint_left.mp hA'S2) hyA hpS2

end RHTower
