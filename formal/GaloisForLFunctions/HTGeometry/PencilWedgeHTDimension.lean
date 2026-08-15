import GaloisForLFunctions.HTGeometry.PencilPPAdmissibleHTDim
import GaloisForLFunctions.HTGeometry.PencilDimensionOneObstruction
import GaloisForLFunctions.HTGeometry.PPMatrixRankFormulaConsequences
import GaloisForLFunctions.HTGeometry.WedgeFacetLowerBound

/-!
# The nonpure two-thick wedge has intrinsic realization dimension two

The boundary wedge of two simplex boundaries has a periodic-pencil separation in two complex
coordinates, so it is realized hypertranscendentally there.  One coordinate is impossible: each of
its facets omits the whole opposite block together with one vertex of its own, which is at least
three vertices, and three `ℚ`-independent periods force a meromorphic carrier to be constant.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial
open scoped Classical

noncomputable section

variable {r s : ℕ}

theorem boundaryWedgeFacet_nonempty (B : BoundaryWedgeFacetIndex r s) :
    (boundaryWedgeFacet B).Nonempty := by
  cases B with
  | inl u => exact ⟨none, none_mem_boundaryWedgeFacet_left u⟩
  | inr u => exact ⟨none, none_mem_boundaryWedgeFacet_right u⟩

/-- **The boundary-wedge facets form an antichain.** -/
theorem boundaryWedgeFacet_antichain (hr : 2 ≤ r) (hs : 2 ≤ s) :
    FacetAntichain (↑(facetFinset (boundaryWedgeFacet :
      BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) :
      Set (Finset (PPBoundaryWedgeVertex r s))) := by
  classical
  have hrc : 1 < Fintype.card (Fin r) := by rw [Fintype.card_fin]; omega
  have hsc : 1 < Fintype.card (Fin s) := by rw [Fintype.card_fin]; omega
  intro F hF G hG hFG
  obtain ⟨B, rfl⟩ := mem_facetFinset.mp (Finset.mem_coe.mp hF)
  obtain ⟨B', rfl⟩ := mem_facetFinset.mp (Finset.mem_coe.mp hG)
  cases B with
  | inl u =>
      cases B' with
      | inl u' =>
          by_cases huu : u = u'
          · rw [huu]
          · obtain ⟨i, hi⟩ : ∃ i : Fin r, i ≠ u := Fintype.exists_ne_of_one_lt_card hrc u
            exact absurd (hFG ((inl_mem_boundaryWedgeFacet_left (s := s) u u').mpr
              (fun h => huu h.symm))) (by simp)
      | inr u' =>
          obtain ⟨i, hi⟩ : ∃ i : Fin r, i ≠ u := Fintype.exists_ne_of_one_lt_card hrc u
          exact absurd (hFG ((inl_mem_boundaryWedgeFacet_left (s := s) u i).mpr hi))
            (not_inl_mem_boundaryWedgeFacet_right u' i)
  | inr u =>
      cases B' with
      | inl u' =>
          obtain ⟨j, hj⟩ : ∃ j : Fin s, j ≠ u := Fintype.exists_ne_of_one_lt_card hsc u
          exact absurd (hFG ((inr_mem_boundaryWedgeFacet_right (r := r) u j).mpr hj))
            (not_inr_mem_boundaryWedgeFacet_left u' j)
      | inr u' =>
          by_cases huu : u = u'
          · rw [huu]
          · obtain ⟨j, hj⟩ : ∃ j : Fin s, j ≠ u := Fintype.exists_ne_of_one_lt_card hsc u
            exact absurd (hFG ((inr_mem_boundaryWedgeFacet_right (r := r) u u').mpr
              (fun h => huu h.symm))) (by simp)

/-- **Every boundary-wedge facet omits at least three vertices.** -/
theorem three_le_card_sdiff_boundaryWedgeFacet_left (hs : 2 ≤ s) (u : Fin r) :
    3 ≤ ((Finset.univ : Finset (PPBoundaryWedgeVertex r s)) \
      boundaryWedgeFacet (Sum.inl u)).card := by
  classical
  have hsc : 1 < Fintype.card (Fin s) := by rw [Fintype.card_fin]; omega
  obtain ⟨j₀⟩ : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨j₁, hj₁⟩ : ∃ j : Fin s, j ≠ j₀ := Fintype.exists_ne_of_one_lt_card hsc j₀
  have hsub : ({some (Sum.inl u), some (Sum.inr j₀), some (Sum.inr j₁)} :
      Finset (PPBoundaryWedgeVertex r s))
      ⊆ (Finset.univ : Finset (PPBoundaryWedgeVertex r s)) \ boundaryWedgeFacet (Sum.inl u) := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simp
    · exact not_inr_mem_boundaryWedgeFacet_left u j₀
    · exact not_inr_mem_boundaryWedgeFacet_left u j₁
  have hcard : ({some (Sum.inl u), some (Sum.inr j₀), some (Sum.inr j₁)} :
      Finset (PPBoundaryWedgeVertex r s)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simpa using hj₁.symm),
      Finset.card_singleton]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-! ### The intrinsic dimension of the boundary wedge -/

set_option maxHeartbeats 1000000 in
/-- **The boundary wedge is realized hypertranscendentally in two complex coordinates.** -/
theorem htRealizableDim_boundaryWedge_two (hr : 1 ≤ r) :
    HTRealizableDim (facetFinset (boundaryWedgeFacet :
      BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) 2 := by
  classical
  haveI : Nonempty (BoundaryWedgeFacetIndex r s) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  refine htRealizableDim_of_ppAdmissible boundaryWedgeFacet boundaryWedgeFacet_nonempty
    (boundaryWedgePencilVector τ r s) (boundaryWedgePencilVector_linearIndependent hτ r s)
    (boundaryWedgePencilForm τ) ?_
  rw [boundaryWedgePencil_evaluation]
  exact boundaryWedgePencilMatrix_ppAdmissible hτ r s

/-- **The boundary wedge is not realized in one complex coordinate.** -/
theorem not_htRealizableDim_boundaryWedge_one (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ HTRealizableDim (facetFinset (boundaryWedgeFacet :
      BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) 1 := by
  classical
  have hu : (0 : ℕ) < r := by omega
  refine not_htRealizableDim_one_of_three_omitted _ (boundaryWedgeFacet_antichain hr hs)
    (V := (Finset.univ : Finset (PPBoundaryWedgeVertex r s)))
    (A := boundaryWedgeFacet (Sum.inl ⟨0, hu⟩))
    (mem_facetFinset.mpr ⟨Sum.inl ⟨0, hu⟩, rfl⟩)
    (boundaryWedgeFacet_nonempty _)
    (three_le_card_sdiff_boundaryWedgeFacet_left hs ⟨0, hu⟩)

/-- **The boundary wedge is not realized in zero coordinates.** -/
theorem not_htRealizableDim_boundaryWedge_zero :
    ¬ HTRealizableDim (facetFinset (boundaryWedgeFacet :
      BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) 0 :=
  not_htRealizableDim_zero _

/-- **Exact intrinsic hypertranscendental realization dimension of every nondegenerate boundary
wedge.** -/
theorem boundaryWedge_htDim_eq_two (hr : 2 ≤ r) (hs : 2 ≤ s) :
    htDim (facetFinset (boundaryWedgeFacet :
      BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) = 2 := by
  have h2 := htRealizableDim_boundaryWedge_two (r := r) (s := s) (by omega)
  have hne : {d | HTRealizableDim (facetFinset (boundaryWedgeFacet :
      BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) d}.Nonempty := ⟨2, h2⟩
  exact htDim_eq_two_of_realizability (Nat.sInf_mem hne) (fun d hd => Nat.sInf_le hd) h2
    not_htRealizableDim_boundaryWedge_zero (not_htRealizableDim_boundaryWedge_one hr hs)

/-- **The intrinsic dimension equals the periodic-pencil dimension for the boundary wedge.** -/
theorem boundaryWedge_htDim_eq_ppDim (hr : 2 ≤ r) (hs : 2 ≤ s) :
    htDim (facetFinset (boundaryWedgeFacet :
        BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s)))
      = ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
        Finset (PPBoundaryWedgeVertex r s)) := by
  rw [boundaryWedge_htDim_eq_two hr hs, boundaryWedge_ppDim_eq_two hr hs]

/-! ### The strict dimension gap -/

/-- The faithful facet-separation dimension of a boundary wedge. -/
def ffsDim (r s : ℕ) : ℕ :=
  sInf {d | Nonempty (UniformBoundaryWedge.FaithfulSeparation r s d)}

/-- **The faithful facet-separation dimension of every nondegenerate boundary wedge is four.** -/
theorem ffsDim_eq_four (hr : 2 ≤ r) (hs : 2 ≤ s) : ffsDim r s = 4 := by
  obtain ⟨h4, hmin⟩ := UniformBoundaryWedge.faithfulSeparation_fin_four_and_minimal_uncond hr hs
  refine le_antisymm (Nat.sInf_le h4) ?_
  have hmem : ffsDim r s ∈ {d | Nonempty (UniformBoundaryWedge.FaithfulSeparation r s d)} :=
    Nat.sInf_mem ⟨4, h4⟩
  exact hmin _ hmem

/-- **The strict dimension law.**  For every nondegenerate boundary wedge the intrinsic
hypertranscendental realization dimension and the periodic-pencil dimension are both two, while the
faithful facet-separation dimension is four: allowing a facet complement to occupy several leaves of
one cyclic period pencil saves exactly two analytic directions. -/
theorem boundaryWedge_htDim_eq_ppDim_lt_ffsDim (hr : 2 ≤ r) (hs : 2 ≤ s) :
    htDim (facetFinset (boundaryWedgeFacet :
        BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) = 2 ∧
      ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
        Finset (PPBoundaryWedgeVertex r s)) = 2 ∧
      ffsDim r s = 4 ∧
      htDim (facetFinset (boundaryWedgeFacet :
        BoundaryWedgeFacetIndex r s → Finset (PPBoundaryWedgeVertex r s))) < ffsDim r s :=
  ⟨boundaryWedge_htDim_eq_two hr hs, boundaryWedge_ppDim_eq_two hr hs, ffsDim_eq_four hr hs, by
    rw [boundaryWedge_htDim_eq_two hr hs, ffsDim_eq_four hr hs]
    omega⟩

end

end GaloisForLFunctions.HTGeometry
