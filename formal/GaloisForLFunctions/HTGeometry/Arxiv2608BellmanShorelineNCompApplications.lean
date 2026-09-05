import GaloisForLFunctions.HTGeometry.Arxiv2608BellmanShorelineCrossPolytope
import GaloisForLFunctions.HTGeometry.Arxiv2608BellmanShorelineNComp

/-!
# Cross-polytope consequences for arXiv:2608.29060 N-COMP

The explicit cross-polytope anchor converts one-sided polygonal approximation into a uniform
positive support certificate.  This closes the finite geometric step between a dimension-dependent
anchor and the paper's dimension-free support-erosion estimate.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- A polygonal set approximating the cross-polytope from one side retains support at least
`1 / √D - h` in every unit direction. -/
theorem bellmanShoreline_polygonalSupport_lower_of_crossPolytope_thickening
    {D : ℕ} (hD : 0 < D)
    {L : Set (EuclideanSpace ℝ (Fin D))} {h : ℝ}
    (hLcompact : IsCompact L)
    (hsub : bellmanShorelineCrossPolytope D ⊆ bellmanShorelineThickening L h)
    (n : EuclideanSpace ℝ (Fin D)) (hn : ‖n‖ = 1) :
    (Real.sqrt D)⁻¹ - h ≤ bellmanShorelineSupport L n := by
  have hzero : (0 : EuclideanSpace ℝ (Fin D)) ∈ bellmanShorelineCrossPolytope D := by
    apply bellmanShoreline_closedBall_subset_crossPolytope hD
    simp
  have herosion := bellmanShorelineSupport_sub_le_polygonalSupport
    (K := bellmanShorelineCrossPolytope D) (L := L) (h := h)
    ⟨0, hzero⟩ hLcompact hsub hn
  have hanchor := bellmanShoreline_crossPolytope_support_lower hD n hn
  linarith

/-- Approximation error strictly below cross-polytope inradius prevents directional collapse. -/
theorem bellmanShoreline_polygonalSupport_pos_of_crossPolytope_thickening
    {D : ℕ} (hD : 0 < D)
    {L : Set (EuclideanSpace ℝ (Fin D))} {h : ℝ}
    (hLcompact : IsCompact L)
    (hsub : bellmanShorelineCrossPolytope D ⊆ bellmanShorelineThickening L h)
    (hh : h < (Real.sqrt D)⁻¹)
    (n : EuclideanSpace ℝ (Fin D)) (hn : ‖n‖ = 1) :
    0 < bellmanShorelineSupport L n := by
  have hlower := bellmanShoreline_polygonalSupport_lower_of_crossPolytope_thickening
    hD hLcompact hsub n hn
  linarith

end GaloisForLFunctions.HTGeometry

end
