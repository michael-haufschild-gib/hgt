import GaloisForLFunctions.HTGeometry.PPMatrixRankFormulaConsequences
import GaloisForLFunctions.HTGeometry.WedgeFacetLowerBound

namespace GaloisForLFunctions

noncomputable section

/-! Periodic-pencil and faithful-separation realizations of the same boundary wedge have
provably different optimal dimensions. -/

/-- Every nondegenerate two-boundary wedge has an exact factor-two representation gap:
periodic pencils need two complex coordinates, while faithful facet separation needs four. -/
theorem boundaryWedge_representationDimensionGapUniversality
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    let p := ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s))
    p = 2 ∧
      Nonempty (UniformBoundaryWedge.FaithfulSeparation r s (2 * p)) ∧
      ∀ d, Nonempty (UniformBoundaryWedge.FaithfulSeparation r s d) → 2 * p ≤ d := by
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  have hpp : ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) = 2 :=
    boundaryWedge_ppDim_eq_two hr hs
  have hfaith := UniformBoundaryWedge.faithfulSeparation_fin_four_and_minimal
    hr hs hτ
  dsimp only
  refine ⟨hpp, ?_⟩
  rw [hpp]
  change Nonempty (UniformBoundaryWedge.FaithfulSeparation r s 4) ∧
    ∀ d, Nonempty (UniformBoundaryWedge.FaithfulSeparation r s d) → 4 ≤ d
  exact hfaith

end

end GaloisForLFunctions
