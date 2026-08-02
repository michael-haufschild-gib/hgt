import GaloisForLFunctions.HTGeometry.BoundaryWedgeExponentialRealization
import GaloisForLFunctions.HTGeometry.BoundaryWedgeRepresentationDimensionGapUniversalityLaw

/-!
# Uniform HT dimension gap for wedges of simplex boundaries

This capstone packages the three exact representation dimensions proved for the same
nondegenerate boundary-wedge family: entire HT realizations and periodic pencils both have
minimal dimension two, while faithful facet separation has minimal dimension four.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Every nondegenerate boundary wedge has intrinsic entire-realization dimension two,
periodic-pencil dimension two, and faithful facet-separation dimension four. -/
theorem boundaryWedge_uniformHTDimensionGap
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    let p := ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s))
    p = 2 ∧
      UniformBoundaryWedge.BoundaryWedgeHTRealizable r s p ∧
      (∀ d, UniformBoundaryWedge.BoundaryWedgeHTRealizable r s d → p ≤ d) ∧
      Nonempty (UniformBoundaryWedge.FaithfulSeparation r s (2 * p)) ∧
      (∀ d, Nonempty (UniformBoundaryWedge.FaithfulSeparation r s d) → 2 * p ≤ d) ∧
      p < 2 * p := by
  have hpp : ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) = 2 :=
    boundaryWedge_ppDim_eq_two hr hs
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  have hfaith :=
    UniformBoundaryWedge.faithfulSeparation_fin_four_and_minimal hr hs hτ
  dsimp only
  refine ⟨hpp, ?_⟩
  rw [hpp]
  refine ⟨UniformBoundaryWedge.boundaryWedgeHTRealizable_two_uncond r s, ?_, ?_, ?_, by omega⟩
  · intro d hd
    by_contra hnot
    have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl
    · exact UniformBoundaryWedge.not_boundaryWedgeHTRealizable_zero r s hd
    · exact UniformBoundaryWedge.not_boundaryWedgeHTRealizable_one hr hs hd
  · simpa using hfaith.1
  · simpa using hfaith.2

end

end GaloisForLFunctions
