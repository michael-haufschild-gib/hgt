import GaloisForLFunctions.RHTower.WeilDeviationTranslationBound

set_option autoImplicit false

/-!
# Uniform constants discharged in `RHTower.WeilExcess`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal Real

noncomputable section

namespace RHTower.WeilExcess



/-- `cauchyProfile_le_kernelSmooth` with its constants supplied by
`RHTower.WeilExcess.exists_riemannAutocorr_ge`. -/
theorem cauchyProfile_le_kernelSmooth_uniform :
    ∃ (κ : ℝ), ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ (s : ℝ) (u : ℝ),
      cauchyProfile δ s u ≤ (3 / (2 * κ)) * kernelSmooth (cauchyProfile δ s) u := by
  obtain ⟨κ, h_0_0, h_0_1⟩ := RHTower.WeilExcess.exists_riemannAutocorr_ge
  refine ⟨κ, ?_⟩
  intro δ hδ0 hδ1 s u
  apply cauchyProfile_le_kernelSmooth <;> assumption

end RHTower.WeilExcess
