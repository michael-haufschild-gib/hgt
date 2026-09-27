import GaloisForLFunctions.RHTower.CCMActualHeadCoherentSupportProjection

/-!
# Support savings in the coherent Γ error bound

The coherent field is projected onto the support of the actual translation
increment. Its reciprocal-Γ cost is the full coherent cost minus a nonnegative
discarded energy. The resulting source lower bound gains twice that energy;
all cross terms inside each projected sum remain intact.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section
namespace RHTower

def ccmActualHeadSupportedCoherentField (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ccmIncrementSupportProjection a r
    (ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N f r)

def ccmActualHeadSupportedCoherentGammaCost (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 *
    ccmGammaHigherBinetDualDensity |r|

def ccmActualHeadInvisibleCoherentGammaCost (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) : ℝ :=
  ∫ r : ℝ, ‖ccmActualHeadQuantileCompletedCoherentField (2 * a.1) N f r -
    ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|

/-- The outward terminal cell vanishes after support projection. Only the inward
oriented interval remains; the statement is valid for every actual cutoff. -/
theorem ccmActualHeadSupportedTerminal_eq_inward_cell
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmIncrementSupportProjection a r
        (ccmActualHeadQuantileTerminalCoherentField (2*a.1) N f.1 r) =
      (((Ioc (ccmOutgoingPrimeQuantileBoundary N - 2*a.1) 0).indicator
        (fun s : ℝ => Real.exp ((s + 2*a.1)/2)) r : ℝ) : ℂ) •
          ccmIncrementSupportProjection a r (logTranslationCLM (-(2*a.1)) f.1) := by
  by_cases hb : ccmOutgoingPrimeQuantileBoundary N ≤ 2*a.1
  · simp only [ccmActualHeadQuantileTerminalCoherentField,
      ccmActualHeadQuantileTerminalDisplacementDensity, if_pos hb, map_smul]
  · by_cases hr : 0 ≤ r
    · have hz := ccmIncrementSupportProjection_terminal_shift a f r
      rw [max_eq_left hr] at hz
      simp only [ccmActualHeadQuantileTerminalCoherentField, map_smul, hz, smul_zero]
    · have hleft : r ∉ Ioc 0 (ccmOutgoingPrimeQuantileBoundary N - 2*a.1) := by
        intro h
        linarith [h.1]
      have hright : r ∉ Ioc (ccmOutgoingPrimeQuantileBoundary N - 2*a.1) 0 := by
        intro h
        linarith [h.1]
      simp only [ccmActualHeadQuantileTerminalCoherentField,
        ccmActualHeadQuantileTerminalDisplacementDensity, if_neg hb,
        indicator_of_notMem hleft, indicator_of_notMem hright,
        neg_zero, Complex.ofReal_zero, zero_smul, map_zero]

/-- Literal surviving prime sum plus inward terminal vector, before taking a norm. -/
theorem ccmActualHeadSupportedCoherentField_eq_prime_sum_inward_terminal
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmActualHeadSupportedCoherentField a N f.1 r =
      (∑ n ∈ Finset.range N, (ccmOutgoingQuantileDisplacementCellDensity n r : ℂ) •
        ccmIncrementSupportProjection a r (logTranslationCLM (-Real.log n) f.1)) +
      (((Ioc (ccmOutgoingPrimeQuantileBoundary N - 2*a.1) 0).indicator
        (fun s : ℝ => Real.exp ((s + 2*a.1)/2)) r : ℝ) : ℂ) •
          ccmIncrementSupportProjection a r (logTranslationCLM (-(2*a.1)) f.1) := by
  unfold ccmActualHeadSupportedCoherentField ccmActualHeadQuantileCompletedCoherentField
  rw [map_add, ccmActualHeadSupportedTerminal_eq_inward_cell]
  simp only [ccmActualHeadQuantileBulkCoherentField,
    ccmActualHeadQuantileCellCoherentField, map_sum, map_smul]

private theorem continuous_comp_measurable_field {E : Type*} [TopologicalSpace E]
    (P : ℝ × E → E) (Y : ℝ → E) (hP : Continuous P) (hY : AEStronglyMeasurable Y) :
    AEStronglyMeasurable (fun r : ℝ => P (r, Y r)) :=
  hP.comp_aestronglyMeasurable
    ((continuous_id : Continuous (fun r : ℝ => r)).aestronglyMeasurable.prodMk hY)

private theorem supported_measurable (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    AEStronglyMeasurable (ccmActualHeadSupportedCoherentField a N f) :=
  continuous_comp_measurable_field
    (fun p : ℝ × SoninL2 => ccmIncrementSupportProjection a p.1 p.2)
    (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f)
    (continuous_ccmIncrementSupportProjection_joint a)
    (aestronglyMeasurable_ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f)

private theorem dual_measurable :
    AEStronglyMeasurable (fun r : ℝ => ccmGammaHigherBinetDualDensity |r|) := by
  apply Continuous.aestronglyMeasurable
  unfold ccmGammaHigherBinetDualDensity
  fun_prop

private theorem supported_density_le (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r| ≤
    ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r| := by
  apply mul_le_mul_of_nonneg_right _
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  have h := norm_sq_ccmIncrementSupportProjection a r
    (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r)
  change _ = ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 +
    ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r -
      ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 at h
  linarith [sq_nonneg ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r -
    ccmActualHeadSupportedCoherentField a N f r‖]

theorem integrable_ccmActualHeadSupportedCoherentGammaDensity
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ => ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|) := by
  refine (integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity (2*a.1) N f).mono'
    (((supported_measurable a N f).norm.pow 2).mul dual_measurable) ?_
  filter_upwards with r
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)))]
  exact supported_density_le a N f r

private theorem invisible_integrable (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    Integrable (fun r : ℝ =>
      ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r -
        ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 *
          ccmGammaHigherBinetDualDensity |r|) := by
  refine ((integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity (2*a.1) N f).sub
    (integrable_ccmActualHeadSupportedCoherentGammaDensity a N f)).congr ?_
  filter_upwards with r
  have h := norm_sq_ccmIncrementSupportProjection a r
    (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r)
  change _ = ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 +
    ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r -
      ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 at h
  change ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r| -
    ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r| = _
  rw [h]
  ring

theorem ccmActualHeadCoherentGammaCost_support_split
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    ccmActualHeadCoherentQuantileGammaChiSquare (2*a.1) N f =
      ccmActualHeadSupportedCoherentGammaCost a N f +
        ccmActualHeadInvisibleCoherentGammaCost a N f := by
  unfold ccmActualHeadCoherentQuantileGammaChiSquare
    ccmActualHeadSupportedCoherentGammaCost ccmActualHeadInvisibleCoherentGammaCost
  rw [← integral_add (integrable_ccmActualHeadSupportedCoherentGammaDensity a N f)
    (invisible_integrable a N f)]
  apply integral_congr_ae
  filter_upwards with r
  have h := norm_sq_ccmIncrementSupportProjection a r
    (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r)
  change _ = ‖ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 +
    ‖ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f r -
      ccmActualHeadSupportedCoherentField a N f r‖ ^ 2 at h
  rw [h, add_mul]

theorem ccmActualHeadSupportedCoherentGammaCost_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadSupportedCoherentGammaCost a N f :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadInvisibleCoherentGammaCost_nonneg
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    0 ≤ ccmActualHeadInvisibleCoherentGammaCost a N f :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg _)
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadSupportedCoherentGammaCost_le_full
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) :
    ccmActualHeadSupportedCoherentGammaCost a N f ≤
      ccmActualHeadCoherentQuantileGammaChiSquare (2*a.1) N f := by
  rw [ccmActualHeadCoherentGammaCost_support_split]
  exact le_add_of_nonneg_right (ccmActualHeadInvisibleCoherentGammaCost_nonneg a N f)

private theorem weighted_inner_lower (d v : SoninL2) (g k : ℝ)
    (hg : 0 < g) (hgk : g * k = 1) :
    -(2 * (‖v‖ ^ 2 * k)) ≤ g * ‖d‖ ^ 2 / 2 + 2 * (inner ℂ d v).re := by
  have hi : -(‖d‖ * ‖v‖) ≤ (inner ℂ d v).re :=
    (neg_le_neg ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm d v))).trans
      (neg_abs_le _)
  have hprod : g * k * ‖v‖ ^ 2 = ‖v‖ ^ 2 := by rw [hgk, one_mul]
  have hbase : 0 ≤ g * ‖d‖ ^ 2 / 2 + 2 * k * ‖v‖ ^ 2 - 2 * ‖d‖ * ‖v‖ := by
    apply nonneg_of_mul_nonneg_right (a := g) _ hg
    nlinarith [sq_nonneg (g * ‖d‖ - 2 * ‖v‖)]
  linarith

theorem ccmActualHeadSupportedCoherentGamma_pointwise_lower
    (a : SuzukiPositiveAperture) (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    -(2 * (‖ccmActualHeadSupportedCoherentField a N f.1 r‖ ^ 2 *
      ccmGammaHigherBinetDualDensity |r|)) ≤
    ccmGammaHigherBinetModeDensity |r| * ccmActualHeadTranslationDefect |r| f.1 / 2 +
      2 * (inner ℂ (logTranslationCLM r f.1 - f.1)
        (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re := by
  by_cases hr : r = 0
  · subst r
    simp [ccmActualHeadTranslationDefect, logTranslationCLM_zero_apply,
      ccmGammaHigherBinetDualDensity]
  · have h := weighted_inner_lower (logTranslationCLM r f.1 - f.1)
      (ccmActualHeadSupportedCoherentField a N f.1 r)
      (ccmGammaHigherBinetModeDensity |r|) (ccmGammaHigherBinetDualDensity |r|)
      (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr))
      (ccmGammaHigherBinetModeDensity_mul_dual (abs_pos.mpr hr))
    rw [ccmActualHeadTranslationDefect_abs]
    change _ ≤ _ * ‖logTranslationCLM r f.1 - f.1‖ ^ 2 / 2 + _
    simpa only [ccmActualHeadSupportedCoherentField,
      inner_increment_ccmIncrementSupportProjection] using h

/-- The signed current bound charges only the component that can pair with the increment. -/
theorem ccmActualHeadCompletedQuantileCurrent_supportedGamma_lower
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1;
    -(2 * ccmActualHeadSupportedCoherentGammaCost a N f.1) ≤
      ccmActualHeadGammaHigherBinetModeEnergy f.1 +
        2 * ccmActualHeadCompletedQuantileCurrent a f := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2*a.1)) + 1
  have hmode := integrable_ccmGammaHigherBinetSymmetricEnergy_formDomain a u
  have hchi := integrable_ccmActualHeadSupportedCoherentGammaDensity a N f.1
  have hinner := integrable_ccmActualHeadCompletedCoherentInnerField (2*a.1) N f.1
  have h := integral_mono ((hchi.const_mul 2).neg)
    ((hmode.div_const 2).add (hinner.const_mul 2))
    (ccmActualHeadSupportedCoherentGamma_pointwise_lower a N f)
  simp only [Pi.neg_apply, Pi.add_apply] at h
  rw [integral_neg, integral_const_mul, integral_add (hmode.div_const 2)
    (hinner.const_mul 2), integral_div, integral_const_mul,
    integral_ccmGammaHigherBinetSymmetricEnergy_formDomain a u] at h
  have hcurrent := ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField a f
  change ccmActualHeadCompletedQuantileCurrent a f = _ at hcurrent
  rw [← hcurrent] at h
  dsimp only at ⊢
  change -(2 * ccmActualHeadSupportedCoherentGammaCost a N f.1) ≤
    2 * ccmActualHeadGammaHigherBinetModeEnergy f.1 / 2 +
      2 * ccmActualHeadCompletedQuantileCurrent a f at h
  linarith

/-- Exact additive improvement over the full-field lower bound, with a nonnegative gain. -/
theorem ccmActualHeadCoherentGammaProducer_add_support_saving_le_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    let N := Nat.floor (Real.exp (2*a.1)) + 1
    ccmActualHeadCoherentQuantileGammaProducer a u +
      2 * ccmActualHeadInvisibleCoherentGammaCost a N f.1 ≤
        ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  let N := Nat.floor (Real.exp (2*a.1)) + 1
  have h := ccmActualHeadCompletedQuantileCurrent_supportedGamma_lower a u
  have hsplit := ccmActualHeadCoherentGammaCost_support_split a N f.1
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation a u
  have hout : ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f =
      4 * ‖f‖ ^ 2 + 2 * ccmActualHeadCompletedQuantileCurrent a f := by
    unfold ccmActualHeadOutgoingQuantileAutocorrelationCurrent
      ccmActualHeadCompletedQuantileCurrent ccmOutgoingQuantileCellAutocorrelationCurrent
    ring
  dsimp only at h hsource ⊢
  rw [hsource]
  change _ ≤ _ + ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f
  rw [hout]
  unfold ccmActualHeadCoherentQuantileGammaProducer
  dsimp only
  change (2 * gammaHardyPhaseRate 0 + 4) * ‖f‖ ^ 2 -
    2 * ccmActualHeadCoherentQuantileGammaChiSquare (2*a.1) N f.1 +
    2 * ccmActualHeadInvisibleCoherentGammaCost a N f.1 ≤ _
  change -(2 * ccmActualHeadSupportedCoherentGammaCost a N f.1) ≤
    ccmActualHeadGammaHigherBinetModeEnergy f.1 +
      2 * ccmActualHeadCompletedQuantileCurrent a f at h
  nlinarith

end RHTower
