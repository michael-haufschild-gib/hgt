import GaloisForLFunctions.RHTower.CCMArchimedeanLogWeightEquivalence
import GaloisForLFunctions.RHTower.SuzukiHlogCompactEmbedding

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace RHTower

/-- The exact Gamma form controls the physical Fourier tail of every form
vector, without a finite-source or response regularity assumption. -/
theorem mul_norm_sq_sub_fourierCutoff_exp_le_ccmArchimedeanFormNorm
    (a : SuzukiPositiveAperture) (g : CCMArchimedeanFormDomain a) (A : ℝ) :
    let f : SoninL2 := (ccmArchimedeanFormToAperture a g : SoninL2)
    A * ‖f - fourierCutoff (centralInterval (Real.exp A))
      (measurableSet_centralInterval (Real.exp A)) f‖ ^ 2 ≤
        ccmArchimedeanLogComparisonConstant * ‖g‖ ^ 2 := by
  let f : SoninL2 := (ccmArchimedeanFormToAperture a g : SoninL2)
  have hC : 0 ≤ ccmArchimedeanLogComparisonConstant :=
    zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant
  have hfour : (fourierUnitary f : ℝ → ℂ) =ᵐ[volume] (g.1 : ℝ → ℂ) := by
    change (fourierUnitary (ccmArchimedeanFourierToTime g.1) : ℝ → ℂ) =ᵐ[volume] _
    rw [fourierUnitary_ccmArchimedeanFourierToTime]
    exact ccmArchimedeanWeightedToL2_coeFn g.1
  have hGamma : Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ * ‖g.1 ξ‖ ^ 2) := by
    have h : Integrable (fun ξ : ℝ => ‖g.1 ξ‖ ^ 2) ccmArchimedeanFormMeasure :=
      (Lp.memLp g.1).integrable_norm_pow (by norm_num)
    unfold ccmArchimedeanFormMeasure at h
    have hw := (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp h
    refine hw.congr ?_
    filter_upwards with ξ
    rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]
    rfl
  have hplain : Integrable (fun ξ : ℝ => ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hleft : Integrable (fun ξ : ℝ => A * (centralInterval (Real.exp A))ᶜ.indicator
      (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ) :=
    (hplain.indicator (measurableSet_centralInterval (Real.exp A)).compl).const_mul A
  change A * ‖f - fourierCutoff _ _ f‖ ^ 2 ≤ _
  calc
    _ = ∫ ξ, A * (centralInterval (Real.exp A))ᶜ.indicator
        (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ := by
      rw [norm_sq_sub_fourierCutoff_central_eq_tailIntegral, integral_const_mul]
    _ ≤ ∫ ξ, ccmArchimedeanLogComparisonConstant *
        (ccmArchimedeanFormWeight ξ * ‖g.1 ξ‖ ^ 2) := by
      apply integral_mono_ae hleft (hGamma.const_mul _)
      filter_upwards [hfour] with ξ hξ
      by_cases hx : ξ ∈ (centralInterval (Real.exp A))ᶜ
      · rw [indicator_of_mem hx, hξ]
        have hb := (le_suzukiLogWeight_of_mem_exp_tail A ξ hx).trans
          (suzukiLogWeight_le_ccmArchimedeanComparison ξ)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (sq_nonneg ‖g.1 ξ‖)
      · rw [indicator_of_notMem hx, mul_zero]
        exact mul_nonneg hC (mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _))
    _ = ccmArchimedeanLogComparisonConstant * ‖g‖ ^ 2 := by
      rw [integral_const_mul, ← norm_sq_ccmArchimedeanFourierL2]
      rfl

end RHTower
end
