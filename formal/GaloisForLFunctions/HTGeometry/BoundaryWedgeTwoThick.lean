import GaloisForLFunctions.HTGeometry.BoundaryWedgeFacetComplement

/-!
# The boundary wedge is two-thick, uniformly in the block sizes

`WedgeTwoThick` certifies two-thickness for the single six-vertex model `S¹ ∨ S²` by decision.  This
file proves it for the whole two-parameter family `Δ_{r,s} = ∂σ^r ∨ ∂σ^s`, `r, s ≥ 2`.

The faces are described first: a set is a face exactly when it is a **proper** subset of one of the
two blocks (`isFaceOf_boundaryWedgeFacets_iff`).  A face that is not a facet then misses at least two
vertices of its block (`two_le_card_sdiff_of_face_not_facet`: missing none would make it the block,
missing exactly one would make it a facet), and adding either of those two vertices keeps it a proper
subset of the block, hence a face.  Those are the two distinct immediate coface directions required
by `TwoThick`.

Together with `facetAntichain` and `not_pureOfCard_of_ne` this makes the whole family a nonpure
two-thick facet antichain, uniformly in `r, s ≥ 2` — the geometric hypothesis of the parent
constraint-dimension law, previously available in Lean only for the concrete six-vertex wedge.
-/

open Finset

namespace GaloisForLFunctions.UniformBoundaryWedge

variable {r s : ℕ}

/-! ### The faces -/

/-- The faces of the boundary wedge are exactly the proper subsets of one of the two blocks. -/
theorem isFaceOf_boundaryWedgeFacets_iff {J : Finset (BoundaryWedgeVertex r s)} :
    IsFaceOf (boundaryWedgeFacets r s) J ↔
      (J ⊆ leftBlock r s ∧ J ≠ leftBlock r s) ∨ (J ⊆ rightBlock r s ∧ J ≠ rightBlock r s) := by
  constructor
  · rintro ⟨F, (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩), hJF⟩
    · refine Or.inl ⟨hJF.trans (Finset.erase_subset u _), ?_⟩
      intro hJ
      subst hJ
      exact (Finset.notMem_erase u _) (hJF hu)
    · refine Or.inr ⟨hJF.trans (Finset.erase_subset u _), ?_⟩
      intro hJ
      subst hJ
      exact (Finset.notMem_erase u _) (hJF hu)
  · rintro (⟨hsub, hne⟩ | ⟨hsub, hne⟩)
    · obtain ⟨u, hu, hnu⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
      exact ⟨(leftBlock r s).erase u, Or.inl ⟨u, hu, rfl⟩,
        fun x hx => Finset.mem_erase.mpr ⟨fun h => hnu (h ▸ hx), hsub hx⟩⟩
    · obtain ⟨u, hu, hnu⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
      exact ⟨(rightBlock r s).erase u, Or.inr ⟨u, hu, rfl⟩,
        fun x hx => Finset.mem_erase.mpr ⟨fun h => hnu (h ▸ hx), hsub hx⟩⟩

/-! ### A nonfacet face misses two vertices of its block -/

/-- A proper subset of a block that is not obtained by deleting a single vertex misses at least two
vertices of the block. -/
theorem two_le_card_sdiff_of_face_not_facet {J B : Finset (BoundaryWedgeVertex r s)}
    (hsub : J ⊆ B) (hne : J ≠ B) (hnf : ∀ u ∈ B, J ≠ B.erase u) : 2 ≤ (B \ J).card := by
  rcases Nat.lt_or_ge (B \ J).card 2 with hlt | hge
  · exfalso
    interval_cases h : (B \ J).card
    · have hempty : B \ J = ∅ := Finset.card_eq_zero.mp h
      exact hne (Finset.Subset.antisymm hsub (fun x hx => by
        by_contra hxJ
        exact (Finset.notMem_empty x) (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, hxJ⟩)))
    · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h
      have huB : u ∈ B := (Finset.mem_sdiff.mp (hu ▸ Finset.mem_singleton_self u)).1
      have huJ : u ∉ J := (Finset.mem_sdiff.mp (hu ▸ Finset.mem_singleton_self u)).2
      refine hnf u huB (Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_))
      · refine Finset.mem_erase.mpr ⟨fun hxu => huJ (hxu ▸ hx), hsub hx⟩
      · obtain ⟨hxu, hxB⟩ := Finset.mem_erase.mp hx
        by_contra hxJ
        exact hxu (Finset.mem_singleton.mp (hu ▸ Finset.mem_sdiff.mpr ⟨hxB, hxJ⟩))
  · exact hge

/-! ### Two-thickness -/

/-- **The boundary wedge is two-thick.**  Every nonfacet face lies in one block and misses at least
two of its vertices, so adjoining either of them keeps it a proper subset of that block, hence a
face: two distinct immediate coface directions. -/
theorem boundaryWedge_twoThick : TwoThick (boundaryWedgeFacets r s) := by
  intro J hJ hJnf
  rcases isFaceOf_boundaryWedgeFacets_iff.mp hJ with ⟨hsub, hne⟩ | ⟨hsub, hne⟩
  · have hnf : ∀ u ∈ leftBlock r s, J ≠ (leftBlock r s).erase u := fun u hu h =>
      hJnf (Or.inl ⟨u, hu, h⟩)
    obtain ⟨q, hq, u, hu, hqu⟩ :=
      Finset.one_lt_card.mp (two_le_card_sdiff_of_face_not_facet hsub hne hnf)
    obtain ⟨hqB, hqJ⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨huB, huJ⟩ := Finset.mem_sdiff.mp hu
    refine ⟨q, u, hqu, hqJ, huJ, ?_, ?_⟩
    · refine isFaceOf_boundaryWedgeFacets_iff.mpr (Or.inl ⟨?_, ?_⟩)
      · exact Finset.insert_subset hqB hsub
      · intro hins
        rcases Finset.mem_insert.mp (hins ▸ huB) with h | h
        · exact hqu (h.symm)
        · exact huJ h
    · refine isFaceOf_boundaryWedgeFacets_iff.mpr (Or.inl ⟨?_, ?_⟩)
      · exact Finset.insert_subset huB hsub
      · intro hins
        rcases Finset.mem_insert.mp (hins ▸ hqB) with h | h
        · exact hqu h
        · exact hqJ h
  · have hnf : ∀ u ∈ rightBlock r s, J ≠ (rightBlock r s).erase u := fun u hu h =>
      hJnf (Or.inr ⟨u, hu, h⟩)
    obtain ⟨q, hq, u, hu, hqu⟩ :=
      Finset.one_lt_card.mp (two_le_card_sdiff_of_face_not_facet hsub hne hnf)
    obtain ⟨hqB, hqJ⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨huB, huJ⟩ := Finset.mem_sdiff.mp hu
    refine ⟨q, u, hqu, hqJ, huJ, ?_, ?_⟩
    · refine isFaceOf_boundaryWedgeFacets_iff.mpr (Or.inr ⟨?_, ?_⟩)
      · exact Finset.insert_subset hqB hsub
      · intro hins
        rcases Finset.mem_insert.mp (hins ▸ huB) with h | h
        · exact hqu (h.symm)
        · exact huJ h
    · refine isFaceOf_boundaryWedgeFacets_iff.mpr (Or.inr ⟨?_, ?_⟩)
      · exact Finset.insert_subset huB hsub
      · intro hins
        rcases Finset.mem_insert.mp (hins ▸ hqB) with h | h
        · exact hqu h
        · exact hqJ h

/-- **The uniform geometric certificate.**  For every `r, s ≥ 2` the boundary wedge is a two-thick
facet antichain, pure exactly when `r = s`. -/
theorem boundaryWedge_geometry (hr : 2 ≤ r) (hs : 2 ≤ s) :
    FacetAntichain (boundaryWedgeFacets r s) ∧ TwoThick (boundaryWedgeFacets r s) ∧
      (r ≠ s → ∀ d, ¬ PureOfCard (boundaryWedgeFacets r s) d) :=
  ⟨facetAntichain hr hs, boundaryWedge_twoThick, fun h => not_pureOfCard_of_ne h⟩

end GaloisForLFunctions.UniformBoundaryWedge
