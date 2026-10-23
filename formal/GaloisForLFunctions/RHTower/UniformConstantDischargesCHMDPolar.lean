import GaloisForLFunctions.RHTower.CHMDPointwiseGenerator

/-!
# Uniform constants discharged in `RHTower.CHMDPolar`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower.CHMDPolar

open CHMDClosedJump CHMDDoobGraph ThetaSourceWard


/-- `abs_symJump_le_lipschitz` with its constants supplied by
`RHTower.CHMDPolar.exists_theta_bound`. -/
theorem abs_symJump_le_lipschitz_uniform :
    ∃ (C : ℝ), ∀ (v : ℝ → ℝ) (L : NNReal), LipschitzWith L v → ∀ (s : ℝ) (y : ℝ),
      |symJump v s y| ≤ 2 * C * L * |s| := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.CHMDPolar.exists_theta_bound
  refine ⟨C, ?_⟩
  intro v L hL s y
  apply abs_symJump_le_lipschitz <;> assumption

end RHTower.CHMDPolar
