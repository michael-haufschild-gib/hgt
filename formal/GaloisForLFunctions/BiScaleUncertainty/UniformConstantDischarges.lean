import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingDeLaValleePoussinRemainder

/-!
# Uniform constants discharged in `GaloisForLFunctions.BiScaleUncertainty`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter Finsupp MeasureTheory RHTower RHTower.WeilOneSided Set Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty



/-- `abs_nodeArchEnergy_sub_weilEnergy_le_dlvp` with its constants supplied by
`GaloisForLFunctions.BiScaleUncertainty.exists_psi_exp_le_dlvp`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_dlvp_uniform :
    ∃ (K : ℝ) (κ : ℝ) (B : ℝ), ∀ (c : WeilTestFn →₀ ℝ), (∀ f, 0 ≤ c f) → ∀ (L : ℝ), 0 ≤ L → (∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) →
      |nodeArchEnergy c - weilEnergy c| ≤ (Real.exp (L / 2) * (1 + 2 * K * dlvpSchurGain κ L) + B + (1 + L) ^ 2) * massOf c := by
  obtain ⟨K, κ, B, h_0_0, h_0_1, h_0_2, h_0_3⟩ := GaloisForLFunctions.BiScaleUncertainty.exists_psi_exp_le_dlvp
  refine ⟨K, κ, B, ?_⟩
  intro c hc L hL hsupp
  apply abs_nodeArchEnergy_sub_weilEnergy_le_dlvp <;> first | assumption | linarith

/-- `abs_ccmLogChebyshevDeficitPrimitive_le_dlvp` with its constants supplied by
`GaloisForLFunctions.BiScaleUncertainty.exists_abs_psi_exp_sub_le_dlvp`. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_le_dlvp_uniform :
    ∃ (K : ℝ) (c : ℝ) (B : ℝ), ∀ (T : ℝ), 0 ≤ T →
      |ccmLogChebyshevDeficitPrimitive T| ≤ T * (K * Real.exp (c ^ 2 / 2) * (Real.exp T * Real.exp (-c * Real.sqrt T)) + B) := by
  obtain ⟨K, c, B, h_0_0, h_0_1, h_0_2, h_0_3⟩ := GaloisForLFunctions.BiScaleUncertainty.exists_abs_psi_exp_sub_le_dlvp
  refine ⟨K, c, B, ?_⟩
  intro T hT
  apply abs_ccmLogChebyshevDeficitPrimitive_le_dlvp <;> assumption

end GaloisForLFunctions.BiScaleUncertainty
