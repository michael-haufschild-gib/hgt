import GaloisForLFunctions.HTGeometry.BoundaryWedgeUniformHTDimensionGap
import GaloisForLFunctions.HTGeometry.WedgeRealization

namespace GaloisForLFunctions

noncomputable section

/-- Complete Lean-boundary witness for one prescribed source-coherence depth. -/
structure FixedAnalyticDimensionArbitrarySourceCoherencePackage (m : ℕ) where
  r : ℕ
  s : ℕ
  two_le_r : 2 ≤ r
  two_le_s : 2 ≤ s
  depth_eq : boundaryWedgeSourceCoherenceDepth r s = m
  uniformDimensionGap :
    let p := ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s))
    p = 2 ∧
      UniformBoundaryWedge.BoundaryWedgeHTRealizable r s p ∧
      (∀ d, UniformBoundaryWedge.BoundaryWedgeHTRealizable r s d → p ≤ d) ∧
      Nonempty (UniformBoundaryWedge.FaithfulSeparation r s (2 * p)) ∧
      (∀ d, Nonempty (UniformBoundaryWedge.FaithfulSeparation r s d) → 2 * p ≤ d) ∧
      p < 2 * p
  deletedFaceClassification (J : Finset (Fin r ⊕ Fin s)) :
    boundaryWedgeDeletedFace J ↔
      (∀ v ∈ J, boundaryWedgeDeletedLeft v) ∨
      (∀ v ∈ J, boundaryWedgeDeletedRight v)
  everyLeftSetIsFace (J : Finset (Fin r)) :
    boundaryWedgeDeletedFace
      (J.map ⟨Sum.inl, by intro i j h; simpa using h⟩ : Finset (Fin r ⊕ Fin s))
  everyRightSetIsFace (J : Finset (Fin s)) :
    boundaryWedgeDeletedFace
      (J.map ⟨Sum.inr, by intro i j h; simpa using h⟩ : Finset (Fin r ⊕ Fin s))
  noMixedEdge (i : Fin r) (j : Fin s) :
    ¬ boundaryWedgeDeletedFace ({Sum.inl i, Sum.inr j} : Finset (Fin r ⊕ Fin s))
  componentLocallyConstant (J : Finset (Fin r ⊕ Fin s))
      (hJ : boundaryWedgeDeletedFace J) (u v : Fin r ⊕ Fin s)
      (hu : u ∈ J) (hv : v ∈ J) :
    boundaryWedgeComponent u = boundaryWedgeComponent v
  componentNotGloballyConstant :
    ¬ ∀ u v : Fin r ⊕ Fin s,
      boundaryWedgeComponent u = boundaryWedgeComponent v

/-- Every finite depth at least three has a dimension-two boundary-wedge realization together
with the full unconditional deleted-centre combinatorial certificate. -/
noncomputable def fixedAnalyticDimensionArbitrarySourceCoherencePackage
    (m : ℕ) (hm : 3 ≤ m) :
    FixedAnalyticDimensionArbitrarySourceCoherencePackage m := by
  have hs : 2 ≤ m - 1 := by omega
  exact {
    r := 2
    s := m - 1
    two_le_r := by omega
    two_le_s := hs
    depth_eq := by simp [boundaryWedgeSourceCoherenceDepth]; omega
    uniformDimensionGap := boundaryWedge_uniformHTDimensionGap (by omega) hs
    deletedFaceClassification := boundaryWedgeDeletedFace_iff
    everyLeftSetIsFace := boundaryWedgeDeletedFace_left
    everyRightSetIsFace := boundaryWedgeDeletedFace_right
    noMixedEdge := boundaryWedgeDeleted_mixed_pair_not_face
    componentLocallyConstant := fun J hJ u v hu hv =>
      boundaryWedgeComponent_eq_of_face hJ hu hv
    componentNotGloballyConstant :=
      boundaryWedgeComponent_not_constant (by omega)
        (lt_of_lt_of_le (by omega) hs)
  }

/-- Closed capstone: fixed intrinsic analytic dimension supports every finite coherence depth. -/
theorem fixedAnalyticDimensionArbitrarySourceCoherence_unconditional :
    ∀ m : ℕ, 3 ≤ m →
      Nonempty (FixedAnalyticDimensionArbitrarySourceCoherencePackage m) := by
  intro m hm
  exact ⟨fixedAnalyticDimensionArbitrarySourceCoherencePackage m hm⟩

end

end GaloisForLFunctions
