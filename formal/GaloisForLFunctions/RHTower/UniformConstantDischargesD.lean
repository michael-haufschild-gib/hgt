import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.RHTower.WeilPolarConeFirstVariation
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity
import GaloisForLFunctions.RHTower.WeilPositivityMertensConstantObstruction
import GaloisForLFunctions.RHTower.WeilPositivityQuadraticConductorLaw
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction
import GaloisForLFunctions.RHTower.XiPhysicalEndpointRefinementFixedWindowEnergyNoGo
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare
import GaloisForLFunctions.RHTower.ZetaZeroDetectorNearLineDichotomy
import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorBounds

set_option autoImplicit false

/-!
# Uniform constants discharged in `RHTower` (D)

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter MeasureTheory Real Set Topology Zeta23
open scoped BigOperators ComplexConjugate ENNReal NNReal Real

noncomputable section

namespace RHTower



/-- `polarRiemannDifference_zero_bound` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem polarRiemannDifference_zero_bound_uniform :
    ∀ (L : ℝ) (c : ℝ), 0 ≤ c → ∀ (ρ : zetaZeroConfig.carrier),
      (1 + |(ρ : ℂ).im|) * ‖paperFT (polarRiemannDifference L c) (gammaOf ρ)‖ ≤ 3 * truncatedRiemannTailEnergy L ∧ (1 + |(ρ : ℂ).im|) * ‖paperFT (polarRiemannDifference L c) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ 3 * truncatedRiemannTailEnergy L := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L c hc ρ
  apply polarRiemannDifference_zero_bound <;> assumption

/-- `truncatedRiemannKernel_zero_bound` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem truncatedRiemannKernel_zero_bound_uniform :
    ∀ (L : ℝ) (ρ : zetaZeroConfig.carrier),
      (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖ ≤ truncatedRiemannTailEnergy L ∧ (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ truncatedRiemannTailEnergy L := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L ρ
  apply truncatedRiemannKernel_zero_bound <;> assumption

/-- `norm_W_polarRiemannDifference_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_polarRiemannDifference_le_uniform :
    ∀ (L : ℝ) (c : ℝ), 0 ≤ c →
      ‖zetaZeroConfig.W (polarRiemannDifference L c) (polarRiemannDifference L c)‖ ≤ 9 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L c hc
  apply norm_W_polarRiemannDifference_le <;> assumption

/-- `nearRadicalEnergy_le_ratio` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem nearRadicalEnergy_le_ratio_uniform :
    ∃ (Λ : ℝ), ∀ (L : ℝ), 40 ≤ Real.exp (2 * (L - 1)) → ((0 + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10 →
      (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 ≤ 20 * zetaInvSqSum * (1 + 2 * Λ) ^ 2 * ((28 * ((0 + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (0 + 2) * Real.exp (2 * (L - 1)) ^ 2 * Real.exp (-π * Real.exp (2 * (L - 1)))) ^ 2 / (Real.exp (-π * Real.exp (2 * (L - 1)) / 2) / (176 * (8 * Real.exp 1) ^ (2 * (0 + 2))))) * ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro L hY₀ hkY
  apply nearRadicalEnergy_le_ratio <;> assumption

/-- `integral_norm_sq_mertensTest_ge` with its constants supplied by
`RHTower.exists_lipschitz_mertensProbe`. -/
theorem integral_norm_sq_mertensTest_ge_uniform :
    ∃ (Lg : ℝ), ∀ (R : ℝ) (S : ℝ), 0 ≤ R → 0 < S →
      1 / 2 * ‖paperFT (weilRadicalTest R) 0‖ ^ 2 * (S * ∫ x : ℝ, ‖mertensProbe x‖ ^ 2) - 2 * (R + S) * (Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S) ^ 2 ≤ ∫ x : ℝ, ‖mertensTest R S x‖ ^ 2 := by
  obtain ⟨Lg, h_0_0, h_0_1⟩ := RHTower.exists_lipschitz_mertensProbe
  refine ⟨Lg, ?_⟩
  intro R S hR hS
  apply integral_norm_sq_mertensTest_ge <;> assumption

/-- `norm_W_mertensTest_le` with its constants supplied by
`RHTower.exists_weilRadicalTest_norms_le`. -/
theorem norm_W_mertensTest_le_uniform :
    ∃ (K₀ : ℝ), ∀ (R : ℝ) (S : ℝ), 0 ≤ R → 0 < S →
      ‖zetaZeroConfig.W (mertensTest R S) (mertensTest R S)‖ ≤ (5 / 4) * (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * ((Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) * (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|))) * (Real.exp (R / 2) * (R * K₀)) * (Real.exp (S / 2) * (S * ∫ x : ℝ, ‖mertensProbe x‖)) ^ 2 := by
  obtain ⟨K₀, h_0_0, h_0_1⟩ := RHTower.exists_weilRadicalTest_norms_le
  refine ⟨K₀, ?_⟩
  intro R S hR hS
  apply norm_W_mertensTest_le <;> assumption

/-- `abs_deriv_weilTestEvenPart_mertensTest_le` with its constants supplied by
`RHTower.exists_lipschitz_mertensProbe`. -/
theorem abs_deriv_weilTestEvenPart_mertensTest_le_uniform :
    ∃ (Lg : ℝ), ∀ (R : ℝ) (S : ℝ), 0 ≤ R → R ≤ S → 0 < S → ∀ (u : ℝ),
      |deriv (weilTestEvenPart (mertensTest R S)) u| ≤ 8 * ((∫ v : ℝ, ‖riemannPhiKernel v‖) * ∫ v : ℝ, ‖weilBumpPolarFree v‖) ^ 2 * Lg := by
  obtain ⟨Lg, h_0_0, h_0_1⟩ := RHTower.exists_lipschitz_mertensProbe
  refine ⟨Lg, ?_⟩
  intro R S hR hRS hS u
  apply abs_deriv_weilTestEvenPart_mertensTest_le <;> assumption

/-- `norm_paperFT_weilRadicalTest_conj_le` with its constants supplied by
`RHTower.exists_weilRadicalTest_norms_le`. -/
theorem norm_paperFT_weilRadicalTest_conj_le_uniform :
    ∃ (K₀ : ℝ), ∀ (R : ℝ), 0 ≤ R → ∀ (ρ : ℂ), |(gammaOf ρ).im| ≤ 1 / 2 →
      ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ Real.exp (R / 2) * (R * K₀) * (1 / (1 + |ρ.im|) ^ 2) := by
  obtain ⟨K₀, h_0_0, h_0_1⟩ := RHTower.exists_weilRadicalTest_norms_le
  refine ⟨K₀, ?_⟩
  intro R hR ρ hIm
  apply norm_paperFT_weilRadicalTest_conj_le <;> assumption

/-- `norm_paperFT_twistTest_real_le` with its constants supplied by
`RHTower.exists_norm_paperFT_weilBumpC_le`. -/
theorem norm_paperFT_twistTest_real_le_uniform :
    ∃ (Cκ : ℝ), ∀ (α : ℝ) (τ₀ : ℝ) (R : ℝ) (S : ℝ), 0 < S → ∀ (τ : ℝ),
      ‖paperFT (twistTest α τ₀ R S) τ‖ ≤ ((∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (1 / 2 * |u|)) * (Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖)) ^ 3 * (S * (Cκ / (1 + S * |τ - τ₀|) ^ 2) ^ 2) := by
  obtain ⟨Cκ, h_0_0, h_0_1⟩ := RHTower.exists_norm_paperFT_weilBumpC_le
  refine ⟨Cκ, ?_⟩
  intro α τ₀ R S hS τ
  apply norm_paperFT_twistTest_real_le <;> assumption

/-- `abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le` with its constants supplied by
`RHTower.exists_norm_xiUnitDoubleCompletedOffDiagonalResponseKernel_global_le`. -/
theorem abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le_uniform :
    ∃ (C : ℝ), ∀ (A : ℝ) (m : ℝ) (c : ℝ), 0 < A → 0 ≤ c → 2 ≤ Real.exp (m - A) →
      |xiUnitDoubleCompletedRefinementApertureDirichletEnergy (xiPhysicalPrimeLogWindowPacket (m - A) (m + c)) A m (m + c)| ≤ 4 * A * (C * (1 + (A + c)) ^ (9 : ℕ)) * (A + c + primeLogWindowConst) ^ (2 : ℕ) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_norm_xiUnitDoubleCompletedOffDiagonalResponseKernel_global_le
  refine ⟨C, ?_⟩
  intro A m c hA hc hlow
  apply abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le <;> assumption

/-- `norm_primeArchShiftedReciprocalMoment_one_le` with its constants supplied by
`RHTower.exists_xiSquaredSeamOneCoordinate_norm_bound`. -/
theorem norm_primeArchShiftedReciprocalMoment_one_le_uniform :
    ∃ (M : ℝ), ∀ (n : ℕ),
      ‖primeArchShiftedReciprocalMoment 1 n‖ ≤ M ^ n * ∑' q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q‖ := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_xiSquaredSeamOneCoordinate_norm_bound
  refine ⟨M, ?_⟩
  intro n
  apply norm_primeArchShiftedReciprocalMoment_one_le
  assumption


/-- `norm_Gamma_neg_line_le_of_gap` with its constants supplied by
`RHTower.exists_norm_Gamma_le_exp_neg_abs`. -/
theorem norm_Gamma_neg_line_le_of_gap_uniform :
    ∃ (C : ℝ), ∀ (η : ℝ), 0 < η → ∀ (c : ℝ), -1 / 2 ≤ c → c ≤ -η → ∀ (y : ℝ),
      ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ ≤ 1 / η * C * Real.exp (-|y|) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_norm_Gamma_le_exp_neg_abs
  refine ⟨C, ?_⟩
  intro η hη c hc1 hc2 y
  apply norm_Gamma_neg_line_le_of_gap <;> assumption

/-- `norm_Gamma_neg_line_le` with its constants supplied by
`RHTower.exists_norm_Gamma_le_exp_neg_abs`. -/
theorem norm_Gamma_neg_line_le_uniform :
    ∃ (C : ℝ), ∀ (c : ℝ), -1 / 2 ≤ c → c ≤ -1 / 12 → ∀ (y : ℝ),
      ‖Complex.Gamma ((c : ℂ) + (y : ℂ) * I)‖ ≤ 12 * C * Real.exp (-|y|) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_norm_Gamma_le_exp_neg_abs
  refine ⟨C, ?_⟩
  intro c hc1 hc2 y
  apply norm_Gamma_neg_line_le <;> assumption

end RHTower
#print axioms RHTower.polarRiemannDifference_zero_bound_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.truncatedRiemannKernel_zero_bound_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_W_polarRiemannDifference_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.nearRadicalEnergy_le_ratio_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.integral_norm_sq_mertensTest_ge_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_W_mertensTest_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.abs_deriv_weilTestEvenPart_mertensTest_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_paperFT_weilRadicalTest_conj_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_paperFT_twistTest_real_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.abs_xiUnitDoubleCompletedRefinementApertureDirichletEnergy_supportPacket_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_primeArchShiftedReciprocalMoment_one_le_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_Gamma_neg_line_le_of_gap_uniform -- AXIOM-AUDIT-TEMP
#print axioms RHTower.norm_Gamma_neg_line_le_uniform -- AXIOM-AUDIT-TEMP
