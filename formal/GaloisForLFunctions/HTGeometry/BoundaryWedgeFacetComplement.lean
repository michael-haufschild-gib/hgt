import GaloisForLFunctions.HTGeometry.WedgeFacetLowerBound
import GaloisForLFunctions.HTGeometry.SimplicialConstraintTower

/-!
# Facet complements of a boundary wedge, and the exclusion of one-variable period codimension

For `r, s ≥ 2` the boundary wedge `Δ_{r,s} = ∂σ^r ∨ ∂σ^s` has vertex set a common centre together
with two disjoint blocks, and facets obtained by deleting one vertex from one block.  This file
records the exact facet combinatorics that the intrinsic-dimension argument needs.

* `leftBlock`, `rightBlock` and their cardinalities `r+1`, `s+1`;
* `card_leftFacet`, `card_rightFacet` — facets have `r` and `s` vertices, so the family is pure
  exactly when `r = s` (`pureOfCard_of_eq`, `not_pureOfCard_of_ne`), the card's nonpurity criterion;
* `facetAntichain` — the family is an inclusion antichain;
* `card_sdiff_leftFacet`, `card_sdiff_rightFacet` — a facet complement in the **full** vertex set has
  cardinality `s+1` resp. `r+1`, not `1`: a facet omits the entire opposite block together with the
  deleted vertex;
* **`not_facetComplementRankOne`** — hence the family never has one-variable period codimension
  (`FacetComplementRankOne`), which is the exact combinatorial output of the HT period-rank argument.

`FacetComplementRankOne` is the combinatorial obstruction that an exact one-variable
hypertranscendental realization would have to satisfy, so this is the combinatorial half of the lower
bound `htDim ≥ 2` for the whole two-parameter family; the periodic-pencil witness of
`PPMatrixRankFormulaConsequences` supplies the matching upper bound.

The vertex type and the facet-membership predicates are those of `WedgeFacetLowerBound`, so the
combinatorics proved here is the same family used by the faithful-separation layer
(`mem_leftFacet_iff`, `mem_rightFacet_iff`).
-/

open Finset

namespace GaloisForLFunctions.UniformBoundaryWedge

variable {r s : ℕ}

/-! ### The two blocks -/

/-- The left block: the common centre together with the left simplex vertices. -/
def leftBlock (r s : ℕ) : Finset (BoundaryWedgeVertex r s) :=
  insert none (Finset.univ.image (fun i : Fin r => (some (Sum.inl i) : BoundaryWedgeVertex r s)))

/-- The right block: the common centre together with the right simplex vertices. -/
def rightBlock (r s : ℕ) : Finset (BoundaryWedgeVertex r s) :=
  insert none (Finset.univ.image (fun j : Fin s => (some (Sum.inr j) : BoundaryWedgeVertex r s)))

@[simp]
theorem mem_leftBlock {v : BoundaryWedgeVertex r s} : v ∈ leftBlock r s ↔ boundaryWedgeLeft v := by
  cases v with
  | none => simp [leftBlock, boundaryWedgeLeft]
  | some w =>
    cases w with
    | inl i => simp [leftBlock, boundaryWedgeLeft]
    | inr j => simp [leftBlock, boundaryWedgeLeft]

@[simp]
theorem mem_rightBlock {v : BoundaryWedgeVertex r s} :
    v ∈ rightBlock r s ↔ boundaryWedgeRight v := by
  cases v with
  | none => simp [rightBlock, boundaryWedgeRight]
  | some w =>
    cases w with
    | inl i => simp [rightBlock, boundaryWedgeRight]
    | inr j => simp [rightBlock, boundaryWedgeRight]

theorem none_mem_leftBlock : (none : BoundaryWedgeVertex r s) ∈ leftBlock r s := by
  simp [leftBlock]

theorem none_mem_rightBlock : (none : BoundaryWedgeVertex r s) ∈ rightBlock r s := by
  simp [rightBlock]

theorem inl_mem_leftBlock (i : Fin r) :
    (some (Sum.inl i) : BoundaryWedgeVertex r s) ∈ leftBlock r s := by
  simp [leftBlock]

theorem inr_mem_rightBlock (j : Fin s) :
    (some (Sum.inr j) : BoundaryWedgeVertex r s) ∈ rightBlock r s := by
  simp [rightBlock]

theorem card_leftBlock : (leftBlock r s).card = r + 1 := by
  rw [leftBlock, Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (by
    intro i j hij; simpa using hij), Finset.card_univ, Fintype.card_fin]

theorem card_rightBlock : (rightBlock r s).card = s + 1 := by
  rw [rightBlock, Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (by
    intro i j hij; simpa using hij), Finset.card_univ, Fintype.card_fin]

theorem card_vertex : Fintype.card (BoundaryWedgeVertex r s) = r + s + 1 := by
  simp [BoundaryWedgeVertex]

/-! ### The facets -/

/-- The facets of the boundary wedge: delete one vertex from one of the two blocks. -/
def boundaryWedgeFacets (r s : ℕ) : Set (Finset (BoundaryWedgeVertex r s)) :=
  {F | (∃ u ∈ leftBlock r s, F = (leftBlock r s).erase u) ∨
    (∃ v ∈ rightBlock r s, F = (rightBlock r s).erase v)}

/-- Membership in a left facet is the predicate used by the faithful-separation layer. -/
theorem mem_leftFacet_iff {u : Option (Fin r)} {v : BoundaryWedgeVertex r s} :
    v ∈ (leftBlock r s).erase (boundaryWedgeLeftVertex u)
      ↔ boundaryWedgeLeftFacetMember u v := by
  rw [Finset.mem_erase, mem_leftBlock, boundaryWedgeLeftFacetMember, and_comm]

/-- Membership in a right facet is the predicate used by the faithful-separation layer. -/
theorem mem_rightFacet_iff {u : Option (Fin s)} {v : BoundaryWedgeVertex r s} :
    v ∈ (rightBlock r s).erase (boundaryWedgeRightVertex u)
      ↔ boundaryWedgeRightFacetMember u v := by
  rw [Finset.mem_erase, mem_rightBlock, boundaryWedgeRightFacetMember, and_comm]

theorem card_leftFacet {u : BoundaryWedgeVertex r s} (hu : u ∈ leftBlock r s) :
    ((leftBlock r s).erase u).card = r := by
  rw [Finset.card_erase_of_mem hu, card_leftBlock]
  omega

theorem card_rightFacet {v : BoundaryWedgeVertex r s} (hv : v ∈ rightBlock r s) :
    ((rightBlock r s).erase v).card = s := by
  rw [Finset.card_erase_of_mem hv, card_rightBlock]
  omega

/-! ### Purity -/

/-- Equal block sizes make the family pure. -/
theorem pureOfCard_of_eq (h : r = s) : PureOfCard (boundaryWedgeFacets r s) r := by
  rintro F (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
  · exact card_leftFacet hu
  · rw [card_rightFacet hv, h]

/-- Unequal block sizes make the family nonpure. -/
theorem not_pureOfCard_of_ne (h : r ≠ s) (d : ℕ) : ¬ PureOfCard (boundaryWedgeFacets r s) d := by
  intro hpure
  have hL : ((leftBlock r s).erase none).card = d :=
    hpure (Or.inl ⟨none, none_mem_leftBlock, rfl⟩)
  have hR : ((rightBlock r s).erase none).card = d :=
    hpure (Or.inr ⟨none, none_mem_rightBlock, rfl⟩)
  rw [card_leftFacet none_mem_leftBlock] at hL
  rw [card_rightFacet none_mem_rightBlock] at hR
  exact h (hL.trans hR.symm)

/-! ### Facet complements in the full vertex set -/

theorem card_sdiff_leftFacet {u : BoundaryWedgeVertex r s} (hu : u ∈ leftBlock r s) :
    ((Finset.univ : Finset (BoundaryWedgeVertex r s)) \ (leftBlock r s).erase u).card = s + 1 := by
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, card_leftFacet hu, card_vertex]
  omega

theorem card_sdiff_rightFacet {v : BoundaryWedgeVertex r s} (hv : v ∈ rightBlock r s) :
    ((Finset.univ : Finset (BoundaryWedgeVertex r s)) \ (rightBlock r s).erase v).card = r + 1 := by
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, card_rightFacet hv, card_vertex]
  omega

/-- **The boundary wedge never has one-variable period codimension.**  A facet omits the whole
opposite block together with the deleted vertex, so its complement in the full vertex set has
cardinality `s+1 ≥ 3`, far from the `≤ 1` that an exact one-variable hypertranscendental realization
would force.  This is the combinatorial half of `htDim ≥ 2`, uniformly in `r, s ≥ 2`. -/
theorem not_facetComplementRankOne (hs : 2 ≤ s) :
    ¬ FacetComplementRankOne (Finset.univ : Finset (BoundaryWedgeVertex r s))
      (boundaryWedgeFacets r s) := by
  intro hrank
  have hmem : ((leftBlock r s).erase none) ∈ boundaryWedgeFacets r s :=
    Or.inl ⟨none, none_mem_leftBlock, rfl⟩
  have hcard := (hrank hmem).2
  rw [card_sdiff_leftFacet none_mem_leftBlock] at hcard
  omega

/-! ### The antichain property -/

theorem facetAntichain (hr : 2 ≤ r) (hs : 2 ≤ s) :
    FacetAntichain (boundaryWedgeFacets r s) := by
  have hleft : ∀ u : BoundaryWedgeVertex r s,
      ∃ i : Fin r, (some (Sum.inl i) : BoundaryWedgeVertex r s) ∈ (leftBlock r s).erase u := by
    intro u
    have h0 : (0 : ℕ) < r := by omega
    have h1 : (1 : ℕ) < r := by omega
    have hne : (⟨0, h0⟩ : Fin r) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
    by_cases hu : u = some (Sum.inl (⟨0, h0⟩ : Fin r))
    · refine ⟨⟨1, h1⟩, Finset.mem_erase.mpr ⟨?_, inl_mem_leftBlock _⟩⟩
      rw [hu]
      simp only [ne_eq, Option.some.injEq, Sum.inl.injEq]
      exact fun h => hne h.symm
    · exact ⟨⟨0, h0⟩, Finset.mem_erase.mpr ⟨fun h => hu h.symm, inl_mem_leftBlock _⟩⟩
  have hright : ∀ v : BoundaryWedgeVertex r s,
      ∃ j : Fin s, (some (Sum.inr j) : BoundaryWedgeVertex r s) ∈ (rightBlock r s).erase v := by
    intro v
    have h0 : (0 : ℕ) < s := by omega
    have h1 : (1 : ℕ) < s := by omega
    have hne : (⟨0, h0⟩ : Fin s) ≠ ⟨1, h1⟩ := by simp [Fin.ext_iff]
    by_cases hv : v = some (Sum.inr (⟨0, h0⟩ : Fin s))
    · refine ⟨⟨1, h1⟩, Finset.mem_erase.mpr ⟨?_, inr_mem_rightBlock _⟩⟩
      rw [hv]
      simp only [ne_eq, Option.some.injEq, Sum.inr.injEq]
      exact fun h => hne h.symm
    · exact ⟨⟨0, h0⟩, Finset.mem_erase.mpr ⟨fun h => hv h.symm, inr_mem_rightBlock _⟩⟩
  rintro F (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) G (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) hsub
  · have hwu : w = u := by
      by_contra hne
      exact (Finset.notMem_erase w (leftBlock r s))
        (hsub (Finset.mem_erase.mpr ⟨hne, hw⟩))
    rw [hwu]
  · obtain ⟨i, hi⟩ := hleft u
    have hmem := Finset.mem_of_mem_erase (hsub hi)
    have hcontra : boundaryWedgeRight (some (Sum.inl i) : BoundaryWedgeVertex r s) :=
      mem_rightBlock.mp hmem
    exact absurd hcontra (by simp [boundaryWedgeRight])
  · obtain ⟨j, hj⟩ := hright u
    have hmem := Finset.mem_of_mem_erase (hsub hj)
    have hcontra : boundaryWedgeLeft (some (Sum.inr j) : BoundaryWedgeVertex r s) :=
      mem_leftBlock.mp hmem
    exact absurd hcontra (by simp [boundaryWedgeLeft])
  · have hwu : w = u := by
      by_contra hne
      exact (Finset.notMem_erase w (rightBlock r s))
        (hsub (Finset.mem_erase.mpr ⟨hne, hw⟩))
    rw [hwu]

end GaloisForLFunctions.UniformBoundaryWedge
