import GaloisForLFunctions.RHTower.CHMDBVUniformGraph

/-!
# Uniform constants discharged in `RHTower.CHMDDoobGraph`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower.CHMDDoobGraph

open CHMDClosedJump Filter GaloisForLFunctions.HTGeometry MeasureTheory Set Topology

/-- `bvLift_norm_sq_le_of_bound` with its constants supplied by
`RHTower.CHMDPolar.exists_theta_bound`. -/
theorem bvLift_norm_sq_le_of_bound_uniform :
    ∃ (C : ℝ), ∀ (v : ℝ → ℝ) (hv : BoundedVariationOn v univ), HasCompactSupport v → ∀ (M : ℝ), 0 ≤ M → (∀ x, |v x| ≤ M) →
      ‖bvLift v hv‖ ^ 2 ≤ (massMeasure.real univ + 4 * (Measure.sum primeMeasure).real univ) * M ^ 2 + (4 * C ^ 2 * ∫ t in Ioi (0 : ℝ), t * archLevyDensity t) * M * (eVariationOn v univ).toReal := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.CHMDPolar.exists_theta_bound
  refine ⟨C, ?_⟩
  intro v hv hc M hM hb
  apply bvLift_norm_sq_le_of_bound <;> assumption

end RHTower.CHMDDoobGraph
