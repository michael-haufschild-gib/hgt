import GaloisForLFunctions.HTGeometry.FokasLenellsCausalPhase
import GaloisForLFunctions.HTGeometry.FokasLenellsHardyMultiplierEvaluation

/-!
# Exact causal orientation of the singular Hardy evolution

Actual Cauchy evaluation survives the analytic regularization limit. At the
point i, positive time attenuates evaluation strictly, although boundary
multiplication preserves norm. A concrete Cauchy feature therefore has no
positive-time Hardy preimage, and its negative-time evolution leaves Hardy.
This proves the complete real-time Hardy invariance gate.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

local instance fokasLenellsCausalHardyOrientationInst1 : CompleteSpace UpperHardyL2 := RHTower.isClosed_hardyL2.completeSpace_coe

/-- Interior Cauchy evaluation intertwines the actual singular Hardy evolution with its phase. -/
theorem causalHardyEvolution_CauchyEval (t : ℝ≥0) (w : {z : ℂ // 0 < z.im}) (u : UpperHardyL2) :
    upperHardyCauchyEval w.val w.property (causalHardyEvolution t u) =
      causalAnalyticPhase t w.val * upperHardyCauchyEval w.val w.property u := by
  have ht : Tendsto (fun a => (regularizedCausalPhase t a).hardyMul u) atBot
      (𝓝 (causalHardyEvolution t u)) := by
    apply tendsto_subtype_rng.2
    exact regularizedCausalPhase_operator_tendsto t u.val
  have he := (upperHardyCauchyEval w.val w.property).continuous.continuousAt.tendsto.comp ht
  have hv := (regularizedCausalPhase_value_tendsto t w).mul_const
    (upperHardyCauchyEval w.val w.property u)
  have hl : Tendsto (fun a => (regularizedCausalPhase t a).fn w.val *
      upperHardyCauchyEval w.val w.property u) atBot
      (𝓝 (upperHardyCauchyEval w.val w.property (causalHardyEvolution t u))) := by
    simpa only [Function.comp_def,upperHardyCauchyEval_closedUpperMultiplier] using he
  exact tendsto_nhds_unique hl hv

/-- Every upper Cauchy feature is an exact adjoint eigenvector of the singular causal action. -/
theorem adjoint_causalHardyEvolution_feature (t : ℝ≥0) (w : {z : ℂ // 0 < z.im}) :
    (causalHardyEvolution t).toContinuousLinearMap.adjoint (lowerCauchyFeatureAt w.val w.property) =
      (starRingEnd ℂ) (causalAnalyticPhase t w.val) • lowerCauchyFeatureAt w.val w.property := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,
    _root_.inner_smul_left (lowerCauchyFeatureAt w.val w.property) u
      ((starRingEnd ℂ) (causalAnalyticPhase t w.val)),Complex.conj_conj]
  exact causalHardyEvolution_CauchyEval t w u

private def originCauchyFeature : UpperHardyL2 := lowerCauchyFeatureAt I (by simp)

private theorem positive_time_no_feature_preimage (t : ℝ≥0) (ht : 0 < (t:ℝ)) (u : UpperHardyL2) :
    causalHardyEvolution t u ≠ originCauchyFeature := by
  intro hu
  have he := causalHardyEvolution_CauchyEval t ⟨I,by simp⟩ u
  rw [hu] at he
  change inner ℂ originCauchyFeature originCauchyFeature =
    causalAnalyticPhase t I * inner ℂ originCauchyFeature u at he
  have hphi : ‖causalAnalyticPhase t I‖ < 1 := by
    have hh := norm_causalAnalyticPhase t ⟨I,by simp⟩
    simp only [Complex.I_im,Complex.normSq_I,div_one,mul_one] at hh
    rw [hh,Real.exp_lt_one_iff]
    exact neg_neg_of_pos (div_pos ht (by norm_num))
  have hp : 0 < ‖originCauchyFeature‖ :=
    norm_pos_iff.mpr (lowerCauchyFeatureAt_ne_zero (by simp))
  have huNorm : ‖u‖ = ‖originCauchyFeature‖ := by
    rw [← (causalHardyEvolution t).norm_map u,hu]
  have hinner : ‖inner ℂ originCauchyFeature originCauchyFeature‖ = ‖originCauchyFeature‖^(2 : ℕ) := by
    rw [← inner_self_re_eq_norm (𝕜 := ℂ) originCauchyFeature,inner_self_eq_norm_sq]
  have hh := congrArg norm he
  rw [hinner,norm_mul] at hh
  have hb := norm_inner_le_norm (𝕜 := ℂ) originCauchyFeature u
  rw [huNorm] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (norm_nonneg (causalAnalyticPhase t I))
  have hlt := mul_lt_mul_of_pos_right hphi (sq_pos_of_pos hp)
  nlinarith

/-- A fixed nonzero Cauchy feature is omitted by every positive-time causal Hardy range. -/
theorem causalHardyEvolution_positive_feature_not_mem_range (a : ℝ) :
    lowerCauchyFeatureAt I (by simp) ∉
      Set.range (causalHardyEvolution ⟨Real.exp a,(Real.exp_pos a).le⟩) := by
  rintro ⟨u,hu⟩
  exact positive_time_no_feature_preimage ⟨Real.exp a,(Real.exp_pos a).le⟩ (Real.exp_pos a) u hu

/-- Negative time sends this concrete Hardy Cauchy vector outside the Hardy subspace. -/
theorem evolution_neg_exp_not_mem_hardy (a : ℝ) :
    evolution (-Real.exp a) (lowerCauchyFeatureAt I (by simp)).val ∉ RHTower.hardyL2 := by
  intro h
  let u : UpperHardyL2 := ⟨evolution (-Real.exp a) originCauchyFeature.val,h⟩
  apply positive_time_no_feature_preimage ⟨Real.exp a,(Real.exp_pos a).le⟩ (Real.exp_pos a) u
  apply Subtype.ext
  change evolution (Real.exp a) (evolution (-Real.exp a) originCauchyFeature.val) = originCauchyFeature.val
  rw [← evolution_add,add_neg_cancel,evolution_zero]

/-- The actual raw unitary group preserves upper Hardy exactly for nonnegative real time. -/
theorem evolution_hardy_invariance_iff (t : ℝ) :
    (∀ u : UpperHardyL2, evolution t u.val ∈ RHTower.hardyL2) ↔ 0 ≤ t := by
  constructor
  · intro h
    by_contra ht
    have ht' : t < 0 := lt_of_not_ge ht
    have he : -Real.exp (Real.log (-t)) = t := by rw [Real.exp_log (neg_pos.mpr ht'),neg_neg]
    apply evolution_neg_exp_not_mem_hardy (Real.log (-t))
    rw [he]
    exact h _
  · intro ht u
    exact evolution_nonnegative_mem_hardy ⟨t,ht⟩ u

/-- The causal Hardy isometry is onto only at zero time. -/
theorem causalHardyEvolution_surjective_iff (t : ℝ≥0) : Function.Surjective (causalHardyEvolution t) ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    have ht' : 0 < (t:ℝ) := lt_of_le_of_ne t.property (by
      intro he
      apply ht
      exact Subtype.ext he.symm)
    obtain ⟨u,hu⟩ := h originCauchyFeature
    exact positive_time_no_feature_preimage t ht' u hu
  · rintro rfl
    intro u
    exact ⟨u,causalHardyEvolution_zero u⟩

end
end GaloisForLFunctions.HTGeometry.FokasLenells
