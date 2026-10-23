import GaloisForLFunctions.RHTower.WeilInsertionAnyWeight

/-!
# Uniform constants discharged in `RHTower.WeilDeletion`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter GaloisForLFunctions.HTGeometry MeasureTheory Set Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower.WeilDeletion



/-- `bumpOverlap_ge` with its constants supplied by
`RHTower.WeilDeletion.exists_lipschitz_phiTwo`. -/
theorem bumpOverlap_ge_uniform :
    ∃ (M : ℝ), ∀ (L : ℝ), 0 < L → ∀ (h : ℝ),
      L * (∫ x, phiN 2 x ^ 2) - M * |h| ≤ bumpOverlap L h := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.WeilDeletion.exists_lipschitz_phiTwo
  refine ⟨M, ?_⟩
  intro L hL h
  apply bumpOverlap_ge <;> first | assumption | linarith

end RHTower.WeilDeletion
