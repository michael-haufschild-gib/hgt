import GaloisForLFunctions.RHTower.CCM.CCMCoherentPhaseCostReduction

/-!
# One-sided control of the complete signed prime--Gamma current

Positive current is retained exactly. Only the region where the complete
coherent pairing is negative incurs the reduced Gamma cost. The sign test
occurs after the full prime and terminal sum, never on separate atoms.
The resulting source bound retains both positive current and an adjustable
share of higher Gamma energy, uniformly over the entire source domain.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private def currentDensity (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) (r : ℝ) : ℝ :=
  (inner ℂ (logTranslationCLM r f - f)
    (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r)).re

def ccmActualHeadPositiveCoherentCurrent (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, max 0 (currentDensity a N f r)

def ccmActualHeadNegativePhaseGammaCost (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, if currentDensity a N f r < 0 then
    ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r| else 0

private theorem positive_current_integrable (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : Integrable (fun r : ℝ => max 0 (currentDensity a N f r)) := by
  have hi : Integrable (currentDensity a N f) :=
    integrable_ccmActualHeadCompletedCoherentInnerField (2*a.1) N f
  have hm : AEStronglyMeasurable (fun r : ℝ => max 0 (currentDensity a N f r)) :=
    (show Continuous (fun x : ℝ => max 0 x) from continuous_const.max continuous_id).comp_aestronglyMeasurable
      hi.aestronglyMeasurable
  refine hi.abs.mono' hm ?_
  filter_upwards with r
  rw [Real.norm_of_nonneg (le_max_left _ _)]
  exact max_le (abs_nonneg _) (le_abs_self _)

private theorem negative_cost_integrable (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => if currentDensity a N f r < 0 then
      ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
        ccmGammaHigherBinetDualDensity |r| else 0) := by
  let j := currentDensity a N f
  let v := fun r : ℝ => ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
    ccmGammaHigherBinetDualDensity |r|
  have hj : Integrable j := integrable_ccmActualHeadCompletedCoherentInnerField (2*a.1) N f
  have hv : Integrable v := integrable_ccmActualHeadPhaseReducedGammaDensity a N f
  let w : ℝ → ℝ := (Iio (0 : ℝ)).indicator (fun _ => (1 : ℝ))
  have hw : Measurable w := measurable_const.indicator measurableSet_Iio
  have hm : AEStronglyMeasurable (fun r : ℝ => if j r < 0 then v r else 0) := by
    have h : AEStronglyMeasurable (fun r : ℝ => w (j r) * v r) :=
      ((hw.comp_aemeasurable hj.aemeasurable).aestronglyMeasurable).mul
      hv.aestronglyMeasurable
    refine h.congr ?_
    filter_upwards with r
    by_cases hr : j r < 0 <;> simp [w, hr]
  refine hv.mono' hm ?_
  filter_upwards with r
  have hv0 : 0 ≤ v r := mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  by_cases hr : j r < 0
  · rw [if_pos hr, Real.norm_of_nonneg hv0]
  · rw [if_neg hr, norm_zero]
    exact hv0

theorem ccmActualHeadPositiveCoherentCurrent_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadPositiveCoherentCurrent a N f :=
  integral_nonneg fun _ => le_max_left _ _

theorem ccmActualHeadNegativePhaseGammaCost_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadNegativePhaseGammaCost a N f := by
  apply integral_nonneg
  intro r
  dsimp only
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  · exact le_rfl

theorem ccmActualHeadNegativePhaseGammaCost_le_reduced
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    ccmActualHeadNegativePhaseGammaCost a N f ≤ ccmActualHeadPhaseReducedGammaCost a N f := by
  apply integral_mono (negative_cost_integrable a N f)
    (integrable_ccmActualHeadPhaseReducedGammaDensity a N f)
  intro r
  dsimp only
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

private theorem one_sided_pointwise_lower
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a)
    (η : {η : ℝ // 0 < η}) (r : ℝ) :
    2 * max 0 (currentDensity a N f.1 r) - (2 / (η : ℝ)) *
      (if currentDensity a N f.1 r < 0 then
        ‖ccmActualHeadPhaseReducedCoherentField a N f.1 r‖ ^ 2 *
          ccmGammaHigherBinetDualDensity |r| else 0) ≤
      (η : ℝ) * (ccmGammaHigherBinetModeDensity |r| *
        ccmActualHeadTranslationDefect |r| f.1) / 2 + 2 * currentDensity a N f.1 r := by
  by_cases hj : currentDensity a N f.1 r < 0
  · rw [if_pos hj, max_eq_left hj.le, mul_zero, zero_sub]
    exact ccmActualHeadPhaseReducedGamma_pointwise_lower a N f η r
  · rw [if_neg hj, max_eq_right (le_of_not_gt hj), mul_zero, sub_zero]
    have hg : 0 ≤ ccmGammaHigherBinetModeDensity |r| := by
      by_cases hr : r = 0
      · simp [hr, ccmGammaHigherBinetModeDensity]
      · exact (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le
    have hd : 0 ≤ ccmActualHeadTranslationDefect |r| f.1 := sq_nonneg _
    exact le_add_of_nonneg_left (div_nonneg (mul_nonneg η.property.le (mul_nonneg hg hd))
      (by positivity))

/-- Positive signed current is never charged as an error. All cross-prime
and terminal phases remain assembled inside the sign test and the cost. -/
theorem ccmRestrictedWeilSource_ge_oneSidedPhaseGamma
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (η : {η : ℝ // 0 < η}) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 +
      (1 - (η : ℝ)) * ccmActualHeadGammaHigherBinetModeEnergy f.1 +
      2 * ccmActualHeadPositiveCoherentCurrent a N f.1 -
      (2 / (η : ℝ)) * ccmActualHeadNegativePhaseGammaCost a N f.1 ≤
        ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2*a.1)) + 1
  have hm := integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u
  have hj := integrable_ccmActualHeadCompletedCoherentInnerField (2*a.1) N f.1
  have hp := positive_current_integrable a N f.1
  have hn := negative_cost_integrable a N f.1
  have h := integral_mono ((hp.const_mul 2).sub (hn.const_mul (2 / (η : ℝ))))
    (((hm.const_mul (η : ℝ)).div_const 2).add (hj.const_mul 2))
    (one_sided_pointwise_lower a N f η)
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [integral_sub (hp.const_mul 2) (hn.const_mul (2 / (η : ℝ))),
    integral_const_mul, integral_const_mul,
    integral_add ((hm.const_mul (η : ℝ)).div_const 2) (hj.const_mul 2),
    integral_div, integral_const_mul, integral_const_mul,
    integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u] at h
  have hj' := ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField a f
  change ccmActualHeadCompletedQuantileCurrent a f = _ at hj'
  change 2 * ccmActualHeadPositiveCoherentCurrent a N f.1 -
    (2 / (η : ℝ)) * ccmActualHeadNegativePhaseGammaCost a N f.1 ≤
    (η : ℝ) * (2 * ccmActualHeadGammaHigherBinetModeEnergy f.1) / 2 +
      2 * (∫ r : ℝ, (inner ℂ (logTranslationCLM r f.1 - f.1)
        (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re) at h
  rw [← hj'] at h
  have hout : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * ccmActualHeadCompletedQuantileCurrent a f := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
      ccmActualHeadCompletedQuantileCurrent ccmOutgoingQuantileCellAutocorrelationCurrent
    ring
  rw [ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation]
  dsimp only
  change _ ≤ _ + ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f
  rw [hout]
  nlinarith only [h]

/-- Four independently nonnegative savings improve the earlier full-field
bound: support, reflection, discarded positive-region cost, and positive current. -/
theorem ccmActualHeadCoherentGammaProducer_add_oneSided_savings_le_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmActualHeadCoherentQuantileGammaProducer a u +
      2 * ccmActualHeadInvisibleCoherentGammaCost a N f.1 +
      2 * ccmActualHeadReflectedGammaSaving a N f.1 +
      2 * (ccmActualHeadPhaseReducedGammaCost a N f.1 -
        ccmActualHeadNegativePhaseGammaCost a N f.1) +
      2 * ccmActualHeadPositiveCoherentCurrent a N f.1 ≤
        ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2*a.1)) + 1
  have h := ccmRestrictedWeilSource_ge_oneSidedPhaseGamma a u ⟨1, one_pos⟩
  have hs := ccmActualHeadCoherentGammaCost_support_split a N f.1
  have hp := ccmActualHeadSupportedGammaCost_phase_split a N f.1
  dsimp only at h ⊢
  unfold ccmActualHeadCoherentQuantileGammaProducer
  dsimp only
  change (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 -
    2 * ccmActualHeadCoherentQuantileGammaChiSquare (2*a.1) N f.1 +
    2 * ccmActualHeadInvisibleCoherentGammaCost a N f.1 +
    2 * ccmActualHeadReflectedGammaSaving a N f.1 +
    2 * (ccmActualHeadPhaseReducedGammaCost a N f.1 -
      ccmActualHeadNegativePhaseGammaCost a N f.1) +
    2 * ccmActualHeadPositiveCoherentCurrent a N f.1 ≤ _
  change (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 +
    (1 - 1) * ccmActualHeadGammaHigherBinetModeEnergy f.1 +
    2 * ccmActualHeadPositiveCoherentCurrent a N f.1 -
    (2 / 1) * ccmActualHeadNegativePhaseGammaCost a N f.1 ≤ _ at h
  linarith only [h, hs, hp]

end RHTower
