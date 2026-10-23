import GaloisForLFunctions.RHTower.ThetaRateMobiusSourceTransfer
import GaloisForLFunctions.RHTower.TruncatedRiemannKernelWeilEnergy
import GaloisForLFunctions.RHTower.WeilFullConeConvolutionPositivity
import GaloisForLFunctions.RHTower.WeilFullConeExtremePoint
import GaloisForLFunctions.RHTower.WeilFullConeLacunaryRigidity
import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilFullConeSummableDeficitRigidity
import GaloisForLFunctions.RHTower.WeilNearRadicalDimension

/-!
# Uniform constants discharged in `RHTower` (C)

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



noncomputable section

namespace RHTower

open Complex Filter GaloisForLFunctions.HTGeometry MeasureTheory Polynomial Set Topology Zeta23
open scoped ComplexConjugate Convolution ENNReal FourierTransform NNReal Real

/-- `thetaRateWeight_mul_le_right` with its constants supplied by
`RHTower.exists_thetaCuspFullSource_le_halfGaussian`. -/
theorem thetaRateWeight_mul_le_right_uniform :
    ∃ (C₁ : ℝ), ∀ (a : ℝ) (x : ℝ) (s : ℝ), a ≤ x → -a ≤ s →
      thetaRateWeight s * thetaCuspFullSource (x + s) ≤ C₁ * Real.exp (5 * a / 2) / (2 * Real.pi) * Real.exp (-(Real.exp (2 * a) / 2 * thetaSeedRate s)) := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_thetaCuspFullSource_le_halfGaussian
  refine ⟨C₁, ?_⟩
  intro a x s hax hs
  apply thetaRateWeight_mul_le_right <;> assumption

/-- `thetaRateWeight_mul_le_left` with its constants supplied by
`RHTower.exists_thetaCuspFullSource_le_halfGaussian`. -/
theorem thetaRateWeight_mul_le_left_uniform :
    ∃ (C₁ : ℝ), ∀ (b : ℝ) (x : ℝ) (s : ℝ), x ≤ b →
      thetaRateWeight s * thetaCuspFullSource (x + s) ≤ thetaRateLeftConst C₁ b := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_thetaCuspFullSource_le_halfGaussian
  refine ⟨C₁, ?_⟩
  intro b x s hxb
  apply thetaRateWeight_mul_le_left <;> assumption

/-- `thetaRateWeight_mul_le_bound` with its constants supplied by
`RHTower.exists_thetaCuspFullSource_le_halfGaussian`. -/
theorem thetaRateWeight_mul_le_bound_uniform :
    ∃ (C₁ : ℝ), ∀ (a : ℝ) (b : ℝ) (x : ℝ) (s : ℝ), a ≤ x → x ≤ b →
      thetaRateWeight s * thetaCuspFullSource (x + s) ≤ thetaRateBound C₁ a b s := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_thetaCuspFullSource_le_halfGaussian
  refine ⟨C₁, ?_⟩
  intro a b x s hax hxb
  apply thetaRateWeight_mul_le_bound <;> assumption

/-- `abs_bulkCutoffDeriv_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem abs_bulkCutoffDeriv_le_uniform :
    ∃ (Λ : ℝ), ∀ (L : ℝ) (u : ℝ),
      |bulkCutoffDeriv L u| ≤ 2 * Λ := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro L u
  apply abs_bulkCutoffDeriv_le <;> assumption

/-- `superExpDecay_nearRadicalTailDeriv` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem superExpDecay_nearRadicalTailDeriv_uniform :
    ∀ (K : ℕ) (L : ℝ) (a : Fin (K + 1) → ℂ),
      SuperExpDecay (nearRadicalTailDeriv L a) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro K L a
  apply superExpDecay_nearRadicalTailDeriv <;> assumption

/-- `one_add_abs_re_mul_norm_paperFT_tail_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem one_add_abs_re_mul_norm_paperFT_tail_le_uniform :
    ∀ (K : ℕ) (L : ℝ) (a : Fin (K + 1) → ℂ) (z : ℂ), |z.im| ≤ 1 / 2 →
      (1 + |z.re|) * ‖paperFT (nearRadicalTail L a) z‖ ≤ (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) + ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro K L a z hz
  apply one_add_abs_re_mul_norm_paperFT_tail_le <;> assumption

/-- `norm_W_nearRadicalTest_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_nearRadicalTest_le_uniform :
    ∀ (K : ℕ) (L : ℝ) (a : Fin (K + 1) → ℂ),
      ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖ ≤ (5 / 4) * (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * ((∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) + ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|)) ^ 2 := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro K L a
  apply norm_W_nearRadicalTest_le <;> assumption

/-- `nearRadicalTail_pointwise_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem nearRadicalTail_pointwise_le_uniform :
    ∃ (Λ : ℝ), ∀ (K : ℕ) (L : ℝ) (a : Fin (K + 1) → ℂ), 8 ≤ Real.exp (2 * (L - 1)) → ((K + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10 → ∀ (M₁ : ℝ) (M₂ : ℝ) (M₃ : ℝ) (M₄ : ℝ), (∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4), |(kernelPoly fun i => (a i).re).eval t| ≤ M₁) → (∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4), |(kernelPoly fun i => (a i).im).eval t| ≤ M₂) → (∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4), |(kernelPoly (parityCoeff fun i => (a i).re)).eval t| ≤ M₃) → (∀ t ∈ Icc (Real.exp (2 * (L - 1)) / 8) (Real.exp (2 * (L - 1)) / 4), |(kernelPoly (parityCoeff fun i => (a i).im)).eval t| ≤ M₄) → ∀ (u : ℝ),
      (‖nearRadicalTail L a u‖ + ‖nearRadicalTailDeriv L a u‖) * Real.exp (1 / 2 * |u|) ≤ (1 + 2 * Λ) * (28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) * Real.exp (2 * (L - 1)) ^ 2 * Real.exp (-π * Real.exp (2 * (L - 1)))) * (M₁ + M₂ + M₃ + M₄) * Real.exp (-|u|) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro K L a hY₀ hkY M₁ M₂ M₃ M₄ h₁ h₂ h₃ h₄ u
  apply nearRadicalTail_pointwise_le <;> assumption

/-- `norm_W_convRiemannTest_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_convRiemannTest_le_uniform :
    ∀ (L : ℝ) (g : ℝ → ℂ), Continuous g → HasCompactSupport g →
      ‖zetaZeroConfig.W (convRiemannTest L g) (convRiemannTest L g)‖ ≤ (∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|)) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L g hg hgc
  apply norm_W_convRiemannTest_le <;> assumption

/-- `riemannKernelReal_sub_truncated_le` with its constants supplied by
`RHTower.exists_riemannKernelReal_le`. -/
theorem riemannKernelReal_sub_truncated_le_uniform :
    ∃ (C : ℝ), ∀ (L : ℝ) (t : ℝ),
      0 ≤ riemannKernelReal t - truncatedRiemannKernelReal L t ∧ riemannKernelReal t - truncatedRiemannKernelReal L t ≤ C * Real.exp (-(2 * (L - 1))) * Real.exp (-(2 * |t|)) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_riemannKernelReal_le
  refine ⟨C, ?_⟩
  intro L t
  apply riemannKernelReal_sub_truncated_le <;> assumption

/-- `riemannKernelReal_shift_le` with its constants supplied by
`RHTower.exists_riemannKernelReal_le`. -/
theorem riemannKernelReal_shift_le_uniform :
    ∃ (C : ℝ), ∀ (R : ℝ) (s : ℝ), |s| ≤ R → ∀ (n : ℕ), 1 ≤ n →
      riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n) ≤ 2 * (C * Real.exp (4 * R)) * (1 / (n : ℝ) ^ 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_riemannKernelReal_le
  refine ⟨C, ?_⟩
  intro R s hs n hn
  apply riemannKernelReal_shift_le <;> assumption

/-- `abs_weightTerm_le` with its constants supplied by
`RHTower.exists_riemannKernelReal_le`. -/
theorem abs_weightTerm_le_uniform :
    ∃ (C : ℝ), ∀ (w : ℕ → ℝ) (R : ℝ) (s : ℝ), |s| ≤ R → ∀ (n : ℕ),
      |(if 2 ≤ n then w n / Real.sqrt n else 0) * (riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n))| ≤ 2 * (C * Real.exp (4 * R)) * (|w n| / (n : ℝ) ^ 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_riemannKernelReal_le
  refine ⟨C, ?_⟩
  intro w R s hs n
  apply abs_weightTerm_le <;> assumption

/-- `norm_W_pairRiemannKernel_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_pairRiemannKernel_le_uniform :
    ∀ (L : ℝ) (c : ℝ), 0 ≤ c → ∀ (ε : ℝ),
      ‖zetaZeroConfig.W (pairRiemannKernel L c ε) (pairRiemannKernel L c ε)‖ ≤ (1 + |ε| * Real.exp (c / 2)) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L c hc ε
  apply norm_W_pairRiemannKernel_le <;> assumption

/-- `norm_W_logShiftRiemannDifference_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_logShiftRiemannDifference_le_uniform :
    ∀ (L : ℝ) (c : ℝ), 0 ≤ c →
      ‖zetaZeroConfig.W (logShiftRiemannDifference L c) (logShiftRiemannDifference L c)‖ ≤ (1 + Real.exp (c / 2)) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L c hc
  apply norm_W_logShiftRiemannDifference_le <;> assumption

/-- `norm_W_combRiemannKernel_le` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_combRiemannKernel_le_uniform :
    ∀ (L : ℝ) (M : ℕ),
      ‖zetaZeroConfig.W (combRiemannKernel L M) (combRiemannKernel L M)‖ ≤ (M * Real.exp (M / 2)) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  intro L M
  apply norm_W_combRiemannKernel_le <;> assumption

/-- `norm_W_nearRadicalTest_le_ratio` with its constants supplied by
`GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition`. -/
theorem norm_W_nearRadicalTest_le_ratio_uniform :
    ∃ (Λ : ℝ), ∀ (K : ℕ) (L : ℝ) (a : Fin (K + 1) → ℂ), 40 ≤ Real.exp (2 * (L - 1)) → ((K + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10 →
      ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖ ≤ 20 * zetaInvSqSum * (1 + 2 * Λ) ^ 2 * ((28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) * Real.exp (2 * (L - 1)) ^ 2 * Real.exp (-π * Real.exp (2 * (L - 1)))) ^ 2 / (Real.exp (-π * Real.exp (2 * (L - 1)) / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2))))) * ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 := by
  obtain ⟨Λ, h_0_0, h_0_1⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨Λ, ?_⟩
  intro K L a hY₀ hkY
  apply norm_W_nearRadicalTest_le_ratio <;> assumption

end RHTower
