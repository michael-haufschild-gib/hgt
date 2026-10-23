import GaloisForLFunctions.RHTower.WeilFullConeConvolutionPositivity
import GaloisForLFunctions.RHTower.WeilNullPotentialExpPairing
import GaloisForLFunctions.RHTower.WeilNullPotentialSpectralPairing

set_option autoImplicit false

/-!
# Uniform constants discharged in `RHTower.WeilRegular`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter FourierTransform MeasureTheory Set Topology
open scoped ComplexConjugate Real

noncomputable section

namespace RHTower.WeilRegular

open RHTower.WeilExcess


/-- `integral_riemannAutocorr_mul_le` with its constants supplied by
`RHTower.exists_riemannAutocorr_le_exp`. -/
theorem integral_riemannAutocorr_mul_le_uniform :
    ∃ (C₁ : ℝ), ∀ (P : ℝ → ℝ), (∀ v, 0 ≤ P v) → ∀ (J : ℕ) (CP : ℝ), (∀ v, P v * (1 + |v|) ^ J ≤ CP) → ∀ (c : ℝ),
      ∫ v, riemannAutocorr (v - c) * P v ≤ C₁ * CP * expMoment J * ((1 + |c|) ^ J)⁻¹ := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_riemannAutocorr_le_exp
  refine ⟨C₁, ?_⟩
  intro P hP0 J CP hP c
  apply integral_riemannAutocorr_mul_le <;> assumption

/-- `integral_riemannAutocorr_mul_le_exp` with its constants supplied by
`RHTower.exists_riemannAutocorr_le_exp`. -/
theorem integral_riemannAutocorr_mul_le_exp_uniform :
    ∃ (C₁ : ℝ), ∀ (P : ℝ → ℝ), (∀ v, 0 ≤ P v) → ∀ (b : ℝ) (CP : ℝ), 0 ≤ b → b < 2 → (∀ v, P v ≤ CP * Real.exp (-(b * |v|))) → ∀ (c : ℝ),
      ∫ v, riemannAutocorr (v - c) * P v ≤ C₁ * CP * expAbsMoment (2 - b) * Real.exp (-(b * |c|)) := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_riemannAutocorr_le_exp
  refine ⟨C₁, ?_⟩
  intro P hP0 b CP hb0 hb hP c
  apply integral_riemannAutocorr_mul_le_exp <;> assumption

/-- `integral_riemannAutocorr_mul_le_linexp` with its constants supplied by
`RHTower.exists_riemannAutocorr_le_exp`. -/
theorem integral_riemannAutocorr_mul_le_linexp_uniform :
    ∃ (C₁ : ℝ), ∀ (P : ℝ → ℝ), (∀ v, 0 ≤ P v) → ∀ (b : ℝ) (CP : ℝ), 0 ≤ b → b < 2 → (∀ v, P v ≤ CP * ((1 + |v|) * Real.exp (-(b * |v|)))) → ∀ (c : ℝ),
      ∫ v, riemannAutocorr (v - c) * P v ≤ C₁ * CP * (1 + 2 / (2 - b)) * expAbsMoment ((2 - b) / 2) * ((1 + |c|) * Real.exp (-(b * |c|))) := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_riemannAutocorr_le_exp
  refine ⟨C₁, ?_⟩
  intro P hP0 b CP hb0 hb hP c
  apply integral_riemannAutocorr_mul_le_linexp <;> assumption

end RHTower.WeilRegular
