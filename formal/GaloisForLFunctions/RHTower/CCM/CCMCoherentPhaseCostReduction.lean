import GaloisForLFunctions.RHTower.CCM.CCMCoherentReflectedCancellation

/-!
# A smaller phase-sensitive cost for the complete prime--Gamma source

After the physical support projection, remove the real orthogonal component
along the reflected direction proved invisible to the signed current. The
new cost is no larger than the supported cost; their difference is an exact
nonnegative square integral. This improves the actual source lower bound by
twice that difference. A free positive parameter also retains an adjustable
fraction of higher Gamma energy instead of spending it all.

All operations act on the complete coherent field, including its signed
terminal term. The bound is independent of any finite-dimensional source
cutoff. No source positivity or RH is asserted.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private def removeRealComponent (V Z : SoninL2) : SoninL2 :=
  V - (((inner ℂ V Z).re / ‖Z‖ ^ 2 : ℝ) : ℂ) • Z

private theorem removeRealComponent_norm_split (V Z : SoninL2) :
    ‖V‖ ^ 2 = ‖removeRealComponent V Z‖ ^ 2 + ‖V - removeRealComponent V Z‖ ^ 2 := by
  by_cases hz : Z = 0
  · simp [removeRealComponent, hz]
  · let b : ℝ := (inner ℂ V Z).re / ‖Z‖ ^ 2
    have hn : ‖Z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    have hb : b * ‖Z‖ ^ 2 = (inner ℂ V Z).re := div_mul_cancel₀ _ hn
    have hb₂ := congrArg (fun x : ℝ => b * x) hb
    have hs : ‖(b : ℂ) • Z‖ ^ 2 = b ^ 2 * ‖Z‖ ^ 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hi : (inner ℂ V ((b : ℂ) • Z)).re = b * (inner ℂ V Z).re := by
      simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    have h := norm_sub_sq (𝕜 := ℂ) V ((b : ℂ) • Z)
    change ‖V - (b : ℂ) • Z‖ ^ 2 = ‖V‖ ^ 2 -
      2 * (inner ℂ V ((b : ℂ) • Z)).re + ‖(b : ℂ) • Z‖ ^ 2 at h
    rw [hi, hs] at h
    change ‖V‖ ^ 2 = ‖V - (b : ℂ) • Z‖ ^ 2 + ‖V - (V - (b : ℂ) • Z)‖ ^ 2
    rw [sub_sub_cancel, hs]
    nlinarith only [h, hb₂]

private theorem removeRealComponent_preserves_pair (d V Z : SoninL2)
    (hz : (inner ℂ d Z).re = 0) :
    (inner ℂ d (removeRealComponent V Z)).re = (inner ℂ d V).re := by
  simp only [removeRealComponent, inner_sub_right, Complex.sub_re, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz, mul_zero,
    zero_mul, sub_zero]

def ccmActualHeadPhaseReducedCoherentField (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  removeRealComponent (ccmActualHeadSupportedCoherentField a N f r)
    (ccmActualHeadSupportedReflectedDirection a N f r)

def ccmActualHeadPhaseReducedGammaCost (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
    ccmGammaHigherBinetDualDensity |r|

def ccmActualHeadReflectedGammaSaving (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadSupportedCoherentField a N f r -
    ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|

/-- The complete real source current survives the additional removal exactly. -/
theorem re_inner_increment_phaseReducedCoherentField
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f.1 - f.1)
      (ccmActualHeadPhaseReducedCoherentField a N f.1 r)).re =
    (inner ℂ (logTranslationCLM r f.1 - f.1)
      (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re := by
  rw [ccmActualHeadPhaseReducedCoherentField,
    removeRealComponent_preserves_pair _ _ _
      (re_inner_increment_supportedReflectedDirection_zero a N f r)]
  rw [ccmActualHeadSupportedCoherentField, inner_increment_ccmIncrementSupportProjection]

theorem norm_sq_ccmActualHeadSupportedCoherentField_phase_split
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 =
      ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 +
        ‖ccmActualHeadSupportedCoherentField a N f r -
          ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 :=
  removeRealComponent_norm_split _ _

private theorem projected_measurable {E : Type*} [TopologicalSpace E]
    (P : ℝ × E → E) (Y : ℝ → E) (hP : Continuous P) (hY : AEStronglyMeasurable Y) :
    AEStronglyMeasurable (fun r : ℝ => P (r, Y r)) :=
  hP.comp_aestronglyMeasurable
    ((continuous_id : Continuous (fun r : ℝ => r)).aestronglyMeasurable.prodMk hY)

private theorem reduced_measurable (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadPhaseReducedCoherentField a N f) := by
  let V := ccmActualHeadSupportedCoherentField a N f
  let Z := ccmActualHeadSupportedReflectedDirection a N f
  have hV : AEStronglyMeasurable V :=
    projected_measurable
      (fun p : ℝ × SoninL2 => ccmIncrementSupportProjection a p.1 p.2)
      (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f)
      (continuous_ccmIncrementSupportProjection_joint a)
      (aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f)
  have hZ : AEStronglyMeasurable Z :=
    aestronglyMeasurable_ccmActualHeadSupportedReflectedDirection a N f
  have hi : AEStronglyMeasurable (fun r : ℝ => (inner ℂ (V r) (Z r)).re) :=
    Complex.continuous_re.comp_aestronglyMeasurable
      (continuous_inner.comp_aestronglyMeasurable (hV.prodMk hZ))
  have hb : AEStronglyMeasurable (fun r : ℝ => (inner ℂ (V r) (Z r)).re / ‖Z r‖ ^ 2) :=
    (hi.aemeasurable.div (hZ.norm.pow 2).aemeasurable).aestronglyMeasurable
  exact hV.sub ((Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hb).smul hZ)

private theorem dual_measurable :
    AEStronglyMeasurable (fun r : ℝ => ccmGammaHigherBinetDualDensity |r|) := by
  apply Continuous.aestronglyMeasurable
  unfold ccmGammaHigherBinetDualDensity
  fun_prop

theorem integrable_ccmActualHeadPhaseReducedGammaDensity
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  refine (integrable_ccmActualHeadSupportedCoherentGammaDensity a N f).mono'
    (((reduced_measurable a N f).norm.pow 2).mul dual_measurable) ?_
  filter_upwards with r
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))]
  apply mul_le_mul_of_nonneg_right _
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  rw [norm_sq_ccmActualHeadSupportedCoherentField_phase_split]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem saving_integrable (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => ‖ccmActualHeadSupportedCoherentField a N f r -
      ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 *
        ccmGammaHigherBinetDualDensity |r|) := by
  refine ((integrable_ccmActualHeadSupportedCoherentGammaDensity a N f).sub
    (integrable_ccmActualHeadPhaseReducedGammaDensity a N f)).congr ?_
  filter_upwards with r
  change ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 * _ -
    ‖ccmActualHeadPhaseReducedCoherentField a N f r‖ ^ 2 * _ = _
  rw [norm_sq_ccmActualHeadSupportedCoherentField_phase_split]
  ring

/-- The removed cost is an actual square integral, not an assumed sign. -/
theorem ccmActualHeadSupportedGammaCost_phase_split
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    ccmActualHeadSupportedCoherentGammaCost a N f =
      ccmActualHeadPhaseReducedGammaCost a N f + ccmActualHeadReflectedGammaSaving a N f := by
  unfold ccmActualHeadSupportedCoherentGammaCost ccmActualHeadPhaseReducedGammaCost
    ccmActualHeadReflectedGammaSaving
  rw [← integral_add (integrable_ccmActualHeadPhaseReducedGammaDensity a N f)
    (saving_integrable a N f)]
  apply integral_congr_ae
  filter_upwards with r
  rw [norm_sq_ccmActualHeadSupportedCoherentField_phase_split, add_mul]

theorem ccmActualHeadPhaseReducedGammaCost_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadPhaseReducedGammaCost a N f :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadReflectedGammaSaving_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadReflectedGammaSaving a N f :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadPhaseReducedGammaCost_le_supported
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    ccmActualHeadPhaseReducedGammaCost a N f ≤ ccmActualHeadSupportedCoherentGammaCost a N f := by
  rw [ccmActualHeadSupportedGammaCost_phase_split]
  exact le_add_of_nonneg_right (ccmActualHeadReflectedGammaSaving_nonneg a N f)

private theorem weighted_inner_lower (d v : SoninL2) (g k : ℝ)
    (hg : 0 < g) (hgk : g*k = 1) :
    -(2 * (‖v‖ ^ 2 * k)) ≤ g * ‖d‖ ^ 2 / 2 + 2 * (inner ℂ d v).re := by
  have hi : -(‖d‖ * ‖v‖) ≤ (inner ℂ d v).re :=
    (neg_le_neg ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm d v))).trans
      (neg_abs_le _)
  have hp : g*k*‖v‖ ^ 2 = ‖v‖ ^ 2 := by rw [hgk, one_mul]
  have hb : 0 ≤ g * ‖d‖ ^ 2 / 2 + 2*k*‖v‖ ^ 2 - 2*‖d‖*‖v‖ := by
    apply nonneg_of_mul_nonneg_right (a := g) _ hg
    nlinarith [sq_nonneg (g*‖d‖ - 2*‖v‖)]
  linarith

/-- Pointwise bound for the complete current, with an adjustable Gamma share. -/
theorem ccmActualHeadPhaseReducedGamma_pointwise_lower
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a)
    (η : {η : ℝ // 0 < η}) (r : ℝ) :
    -((2 / (η : ℝ)) * (‖ccmActualHeadPhaseReducedCoherentField a N f.1 r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|)) ≤
    (η : ℝ) * (ccmGammaHigherBinetModeDensity |r| *
      ccmActualHeadTranslationDefect |r| f.1) / 2 +
        2 * (inner ℂ (logTranslationCLM r f.1 - f.1)
          (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re := by
  by_cases hr : r = 0
  · subst r
    simp [ccmActualHeadTranslationDefect, logTranslationCLM_zero_apply,
      ccmGammaHigherBinetDualDensity]
  · let g := ccmGammaHigherBinetModeDensity |r|
    let k := ccmGammaHigherBinetDualDensity |r|
    have hg : 0 < g := ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)
    have hk : g*k = 1 := ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr)
    have hp : ((η : ℝ)*g) * (k / (η : ℝ)) = 1 := by
      calc
        _ = g*k := by field_simp [η.property.ne']
        _ = 1 := hk
    have h := weighted_inner_lower (logTranslationCLM r f.1 - f.1)
      (ccmActualHeadPhaseReducedCoherentField a N f.1 r) ((η : ℝ)*g) (k / (η : ℝ))
      (mul_pos η.property hg) hp
    rw [re_inner_increment_phaseReducedCoherentField] at h
    rw [ccmActualHeadTranslationDefect_abs]
    change _ ≤ (η : ℝ) * (g * ‖logTranslationCLM r f.1 - f.1‖ ^ 2) / 2 + _
    convert h using 1 <;> ring

/-- All source vectors share this bound; the parameter preserves a chosen
fraction of higher Gamma energy while paying only the reduced coherent cost. -/
theorem ccmRestrictedWeilSource_ge_phaseReducedGamma
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (η : {η : ℝ // 0 < η}) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 +
      (1 - (η : ℝ)) * ccmActualHeadGammaHigherBinetModeEnergy f.1 -
      (2 / (η : ℝ)) * ccmActualHeadPhaseReducedGammaCost a N f.1 ≤
        ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2*a.1)) + 1
  have hm := integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u
  have hc := integrable_ccmActualHeadPhaseReducedGammaDensity a N f.1
  have hi := integrable_ccmActualHeadCompletedCoherentInnerField (2*a.1) N f.1
  have h := integral_mono ((hc.const_mul (2 / (η : ℝ))).neg)
    (((hm.const_mul (η : ℝ)).div_const 2).add (hi.const_mul 2))
    (ccmActualHeadPhaseReducedGamma_pointwise_lower a N f η)
  simp only [Pi.neg_apply, Pi.add_apply] at h
  rw [integral_neg, integral_const_mul,
    integral_add ((hm.const_mul (η : ℝ)).div_const 2) (hi.const_mul 2),
    integral_div, integral_const_mul, integral_const_mul,
    integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u] at h
  have hj := ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField a f
  change ccmActualHeadCompletedQuantileCurrent a f = _ at hj
  rw [← hj] at h
  change -((2 / (η : ℝ)) * ccmActualHeadPhaseReducedGammaCost a N f.1) ≤
    (η : ℝ) * (2 * ccmActualHeadGammaHigherBinetModeEnergy f.1) / 2 +
      2 * ccmActualHeadCompletedQuantileCurrent a f at h
  have hout : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * ccmActualHeadCompletedQuantileCurrent a f := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
      ccmActualHeadCompletedQuantileCurrent ccmOutgoingQuantileCellAutocorrelationCurrent
    ring
  rw [ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation]
  dsimp only
  change _ ≤ _ + ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f
  rw [hout]
  linarith only [h]

/-- Independent nonnegative improvement over the previous supported source
bound. Both the old support saving and the new reflected saving are retained. -/
theorem ccmActualHeadCoherentGammaProducer_add_reflected_saving_le_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmActualHeadCoherentQuantileGammaProducer a u +
      2 * ccmActualHeadInvisibleCoherentGammaCost a N f.1 +
      2 * ccmActualHeadReflectedGammaSaving a N f.1 ≤
        ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2*a.1)) + 1
  have h := ccmRestrictedWeilSource_ge_phaseReducedGamma a u ⟨1, one_pos⟩
  have hs := ccmActualHeadCoherentGammaCost_support_split a N f.1
  have hp := ccmActualHeadSupportedGammaCost_phase_split a N f.1
  dsimp only at h ⊢
  unfold ccmActualHeadCoherentQuantileGammaProducer
  dsimp only
  change (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 -
    2 * ccmActualHeadCoherentQuantileGammaChiSquare (2*a.1) N f.1 +
    2 * ccmActualHeadInvisibleCoherentGammaCost a N f.1 +
    2 * ccmActualHeadReflectedGammaSaving a N f.1 ≤ _
  change (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 +
    (1 - 1) * ccmActualHeadGammaHigherBinetModeEnergy f.1 -
    (2 / 1) * ccmActualHeadPhaseReducedGammaCost a N f.1 ≤ _ at h
  linarith only [h, hs, hp]

end RHTower
