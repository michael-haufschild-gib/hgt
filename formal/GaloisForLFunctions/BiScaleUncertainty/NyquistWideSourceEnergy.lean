import GaloisForLFunctions.BiScaleUncertainty.BroadSpectralCostRealization

/-! # Quantitative energy decay for actual stretched compact sources -/

open Set Filter Topology MeasureTheory
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- A fixed source supplies one constant valid for every positive dilation. -/
theorem exists_sourceRescale_linear_energy_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ →
      0 ≤ normalizedArchEnergy (sourceRescale f δ) ∧
        normalizedArchEnergy (sourceRescale f δ) ≤ δ * K := by
  obtain ⟨M, hM, hbound⟩ := exists_autocorr_increment_linear_bound hf hfc
  let K : ℝ := M * archWeightFirstMoment / autocorr f 0
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hM archWeightFirstMoment_nonneg) hR.le
  refine ⟨K, hK, ?_⟩
  intro δ hδ
  have hreg := contDiff_sourceRescale hf δ
  have hcomp := hasCompactSupport_sourceRescale hfc hδ
  have hmass : autocorr (sourceRescale f δ) 0 = δ⁻¹ * autocorr f 0 := by
    simpa only [mul_zero] using autocorr_sourceRescale f hδ 0
  have hpos : 0 < autocorr (sourceRescale f δ) 0 := by rw [hmass]; positivity
  have hraw : biScaleLevyEnergy (sourceRescale f δ) ≤ M * archWeightFirstMoment := by
    unfold biScaleLevyEnergy archWeightFirstMoment
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_biScaleLevyIntegrand hreg hcomp)
      (integrableOn_mul_archLevySinhWeight.const_mul M) measurableSet_Ioi (fun x hx => ?_)
    rw [hmass, autocorr_sourceRescale f hδ]
    have hb := hbound (δ * x)
    rw [abs_of_pos (mul_pos hδ hx)] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hδ).le
    have heq : δ⁻¹ * (M * (δ * x)) = M * x := by field_simp [hδ.ne']
    rw [heq] at hmul
    have hi : δ⁻¹ * autocorr f 0 - δ⁻¹ * autocorr f (δ * x) ≤ M * x := by
      simpa only [mul_sub] using hmul
    calc
      _ ≤ (M * x) * archLevySinhWeight x :=
        mul_le_mul_of_nonneg_right hi (archLevySinhWeight_pos hx).le
      _ = _ := by ring
  constructor
  · exact div_nonneg (biScaleLevyEnergy_nonneg hcomp hreg.continuous) hpos.le
  · unfold normalizedArchEnergy
    rw [hmass]
    calc
      _ ≤ (M * archWeightFirstMoment) / (δ⁻¹ * autocorr f 0) :=
        div_le_div_of_nonneg_right hraw (by positivity)
      _ = δ * K := by unfold K; field_simp [hδ.ne', hR.ne']

end
end GaloisForLFunctions.BiScaleUncertainty
