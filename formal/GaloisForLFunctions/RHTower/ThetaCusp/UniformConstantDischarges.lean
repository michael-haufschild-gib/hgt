import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeFarField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeLineIntegral

/-!
# Uniform constants discharged in `RHTower`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower

open Bottcher Complex MeasureTheory ModularGroup Set UpperHalfPlane
open scoped MatrixGroups Real

/-- `re_chLineInt_ge` with its constants supplied by
`RHTower.exists_thetaGroupBasis_one_cusp`. -/
theorem re_chLineInt_ge_uniform :
    ∃ (M : ℝ), 0 < t → t ≤ 1 / 1000000000 →
      chG0 t * t ^ 3 / 16 - 2 * chBfar t M ≤ (chLineInt t).re := by
  obtain ⟨M, h_0_0⟩ := RHTower.exists_thetaGroupBasis_one_cusp
  refine ⟨M, ?_⟩
  intro ht ht0
  apply re_chLineInt_ge <;> assumption

/-- `norm_chLine_far` with its constants supplied by
`RHTower.exists_thetaGroupBasis_one_cusp`. -/
theorem norm_chLine_far_uniform :
    ∃ (M : ℝ), 0 < t → t ^ 4 ≤ 1 / 6 → ∀ (s : ℝ), 2 * t ^ 2 ≤ |s| →
      ‖chLine t s‖ ≤ chBfar t M * Real.exp (-|s|) := by
  obtain ⟨M, h_0_0⟩ := RHTower.exists_thetaGroupBasis_one_cusp
  refine ⟨M, ?_⟩
  intro ht ht4 s hs
  apply norm_chLine_far <;> assumption

end RHTower
