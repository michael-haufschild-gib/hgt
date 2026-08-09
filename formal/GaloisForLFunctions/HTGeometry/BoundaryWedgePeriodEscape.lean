import GaloisForLFunctions.HTGeometry.PeriodEscapeDimension

/-!
# The period-escape dimension of the boundary wedge

For `r, s ≥ 2` the boundary wedge `∂σʳ ∨ ∂σˢ` has period-escape dimension exactly two.

The upper bound is its periodic-pencil configuration: each facet's pencil form gives the escape
group `{z : ℓ z ∈ ℤ}`, whose quotient carries a continuous surjection onto the real line.

The lower bound is combinatorial.  A facet obtained by deleting a vertex from one block omits the
whole opposite block, hence at least two vertices; their translation vectors would both lie in one
escape subgroup of `ℂ`, which has `ℚ`-rank at most one.

* **`boundaryWedge_peDim_eq_two`**.
-/

namespace GaloisForLFunctions

/-- Every boundary-wedge facet contains the common centre, hence is nonempty. -/
theorem boundaryWedgeFacet_nonempty {r s : ℕ} (B : BoundaryWedgeFacetIndex r s) :
    (boundaryWedgeFacet B).Nonempty := by
  cases B with
  | inl u => exact ⟨none, none_mem_boundaryWedgeFacet_left u⟩
  | inr u => exact ⟨none, none_mem_boundaryWedgeFacet_right u⟩

/-- **Exact period-escape dimension of every nondegenerate boundary wedge.**  The periodic pencil
attains two, and no facet system omitting two vertices from one facet can be separated in complex
dimension one. -/
theorem boundaryWedge_peDim_eq_two {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    peDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) = 2 := by
  have hpp := boundaryWedge_ppDim_eq_two hr hs
  have hpos : 0 < ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) := by rw [hpp]; norm_num
  have hle : peDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) ≤ 2 := by
    have := peDim_le_ppDim boundaryWedgeFacet_nonempty hpos
    rwa [hpp] at this
  have hex := exists_periodEscapeSeparation_of_ppDim_pos
    (faces := (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s))) boundaryWedgeFacet_nonempty hpos
  set u : Fin r := ⟨0, by omega⟩ with hu
  set j₀ : Fin s := ⟨0, by omega⟩ with hj₀
  set j₁ : Fin s := ⟨1, by omega⟩ with hj₁
  have hne : (some (Sum.inr j₀) : PPBoundaryWedgeVertex r s) ≠ some (Sum.inr j₁) := by
    simp only [ne_eq, Option.some.injEq, Sum.inr.injEq]
    intro h
    rw [hj₀, hj₁] at h
    exact absurd (congrArg Fin.val h) (by norm_num)
  have hge : 2 ≤ peDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) :=
    two_le_peDim hex (Sum.inl u)
      (not_inr_mem_boundaryWedgeFacet_left u j₀)
      (not_inr_mem_boundaryWedgeFacet_left u j₁) hne
  exact le_antisymm hle hge

end GaloisForLFunctions
