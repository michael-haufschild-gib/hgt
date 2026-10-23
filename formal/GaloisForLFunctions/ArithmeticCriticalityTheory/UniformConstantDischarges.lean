import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateEnergyComparison
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePlateauPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePoleFreeVariationInequality

/-!
# Uniform constants discharged in `GaloisForLFunctions.ArithmeticCriticalityTheory`

Each theorem is a corpus estimate whose constants were hypotheses, with the constants supplied by
the corpus theorems proving the corresponding bounds (named in each docstring).
-/

open Filter MeasureTheory RHTower RHTower.CHMDPolar Set Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- `sameSideEnergy_plateau_le` with its constants supplied by
`GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen`. -/
theorem sameSideEnergy_plateau_le_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ), 0 < a → ∀ (u : ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u → ∀ (Λ : ℝ) (L : ℝ), (∀ x y, |u y - u x| ≤ Λ * |y - x|) → (∀ x, |x| ≤ L → u x = 1) →
      sameSideEnergy (shiftedGroundState a) u ≤ riemannKernelReal 0 * (C * Real.exp (16 * a)) * Λ ^ 2 * ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 3) * Real.exp (-(8 * L)) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen
  refine ⟨C, ?_⟩
  intro a ha u hu huc Λ L hLip hone
  apply sameSideEnergy_plateau_le <;> assumption

/-- `integral_Ioi_shiftDifference_mul_sinh_half_tail_le` with its constants supplied by
`GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen`. -/
theorem integral_Ioi_shiftDifference_mul_sinh_half_tail_le_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ) (L : ℝ), 0 ≤ L →
      (∫ x in Ioi L, shiftDifference a x * Real.sinh (x / 2)) ≤ C * Real.exp (16 * a) * Real.exp (-(8 * L)) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen
  refine ⟨C, ?_⟩
  intro a L hL
  apply integral_Ioi_shiftDifference_mul_sinh_half_tail_le <;> assumption

/-- `integral_sq_mul_shiftDifference_mul_sinh_ge` with its constants supplied by
`GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen`. -/
theorem integral_sq_mul_shiftDifference_mul_sinh_ge_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ), 0 < a → ∀ (u : ℝ → ℝ), Continuous u → HasCompactSupport u → ∀ (L : ℝ), 0 ≤ L → (∀ x, |x| ≤ L → u x = 1) →
      Real.sinh (a / 2) / 2 - C * Real.exp (16 * a) * Real.exp (-(8 * L)) ≤ ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen
  refine ⟨C, ?_⟩
  intro a ha u hu huc L hL hone
  apply integral_sq_mul_shiftDifference_mul_sinh_ge <;> assumption

/-- `reflectedDifferenceEnergy_plateau_le` with its constants supplied by
`GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen`. -/
theorem reflectedDifferenceEnergy_plateau_le_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ), 0 < a → ∀ (u : ℝ → ℝ), ContDiff ℝ 1 u → HasCompactSupport u → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) → ∀ (L : ℝ), (∀ x, |x| ≤ L → u x = 1) →
      reflectedDifferenceEnergy (shiftedGroundState a) u ≤ riemannKernelReal 0 * (C * Real.exp (16 * a)) * ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 2) * Real.exp (-(8 * L)) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen
  refine ⟨C, ?_⟩
  intro a ha u hu huc hnn hle L hone
  apply reflectedDifferenceEnergy_plateau_le <;> assumption

/-- `source_meanCorrectedProfile_ge` with its constants supplied by
`GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen`. -/
theorem source_meanCorrectedProfile_ge_uniform :
    ∃ (C : ℝ), ∀ (a : ℝ), 0 < a → ∀ (u : ℝ → ℝ), Continuous u → HasCompactSupport u → ∀ (R : ℝ) (L : ℝ), (∀ x, R < |x| → u x = 0) → R ≤ L → 0 ≤ L →
      profileVariance a u - 4 * Real.sinh (a / 2) * (2 * profileMoment a u / Real.sinh (a / 2)) ^ 2 * (C * Real.exp (16 * a) * Real.exp (-(8 * L))) ≤ 4 * Real.sinh (a / 2) * ∫ x in Ioi (0 : ℝ), meanCorrectedProfile a u L x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := GaloisForLFunctions.ArithmeticCriticalityTheory.exists_riemannKernelReal_le_exp_sixteen
  refine ⟨C, ?_⟩
  intro a ha u hu huc R L hsupp hRL hL0
  apply source_meanCorrectedProfile_ge <;> assumption

end GaloisForLFunctions.ArithmeticCriticalityTheory
