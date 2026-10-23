import GaloisForLFunctions.SquareRootThreshold.KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape
import GaloisForLFunctions.SquareRootThreshold.PrimeTailCouplingCriterion

/-!
# Uniform constants discharged in `GaloisForLFunctions.SquareRootThreshold`

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Complex Filter Finset GaloisForLFunctions MeasureTheory Set Topology Zeta23 _root_.RHTower _root_.RHTower.WeilRegular
open scoped BigOperators ComplexConjugate Real

/-- `integral_norm_sq_paperFT_shift_mul_mu_le` with its constants supplied by
`GaloisForLFunctions.SquareRootThreshold.exists_mu_le`. -/
theorem integral_norm_sq_paperFT_shift_mul_mu_le_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ) (f : ℝ → ℂ), ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → ∀ (ξ : ℝ),
      ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ ≤ (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) + (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.SquareRootThreshold.exists_mu_le
  refine ⟨C, ?_⟩
  intro a f hf hfs ξ
  apply integral_norm_sq_paperFT_shift_mul_mu_le <;> assumption

/-- `re_archPart_le` with its constants supplied by
`GaloisForLFunctions.SquareRootThreshold.exists_mu_le`. -/
theorem re_archPart_le_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ) (f : ℝ → ℂ), ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → ∀ (ξ : ℝ),
      (archPart f ξ).re ≤ 2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 + (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) + (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.SquareRootThreshold.exists_mu_le
  refine ⟨C, ?_⟩
  intro a f hf hfs ξ
  apply re_archPart_le <;> assumption

/-- `integral_norm_sq_paperFT_mul_mu_le` with its constants supplied by
`GaloisForLFunctions.SquareRootThreshold.exists_mu_le`. -/
theorem integral_norm_sq_paperFT_mul_mu_le_uniform :
    ∃ (C : ℝ), ∀ (c : ℝ → ℂ), ContDiff ℝ 2 c → HasCompactSupport c → ∀ (a : ℝ), (∀ u, c u ≠ 0 → |u| ≤ a) →
      ∫ τ : ℝ, ‖paperFT c τ‖ ^ 2 * mu τ ≤ (4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖)) ^ 2 * (1 / 2 + π * C) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.SquareRootThreshold.exists_mu_le
  refine ⟨C, ?_⟩
  intro c hc hcc a hca
  apply integral_norm_sq_paperFT_mul_mu_le <;> assumption

/-- `re_archPart_zero_le_of_odd` with its constants supplied by
`GaloisForLFunctions.SquareRootThreshold.exists_mu_le`. -/
theorem re_archPart_zero_le_of_odd_uniform :
    ∃ (C : ℝ), ∀ (s : ℝ → ℝ) (a : ℝ), ContDiff ℝ 2 s → (∀ u, s u ≠ 0 → |u| ≤ a) → (∀ u, s (-u) = -s u) →
      (archPart (fun u => (s u : ℂ)) 0).re ≤ -(2 * (∫ u, s u * Real.sinh (1 / 2 * u)) ^ 2) + (4 * testNorm s) ^ 2 * (1 / 2 + π * C) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.SquareRootThreshold.exists_mu_le
  refine ⟨C, ?_⟩
  intro s a hs hsupp hodd
  apply re_archPart_zero_le_of_odd <;> assumption

end GaloisForLFunctions.SquareRootThreshold
