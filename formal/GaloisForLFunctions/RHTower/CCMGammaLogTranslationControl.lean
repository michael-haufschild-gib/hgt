import GaloisForLFunctions.RHTower.CCMGammaLogTranslationKernel

/-!
# A uniform logarithmic translation bound from the remaining Gamma energy

The estimate applies to each complete archimedean form-domain head. Its
constant does not depend on aperture, polynomial degree, or coefficients.
Only the higher Binet energy is used, preserving the existing cancellation
of the first mode against the polar term. This does not assert positivity
of the completed prime--Gamma source.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- Remaining Gamma energy controls every short translation of the complete
source, without a degree-dependent derivative estimate. -/
theorem ccmActualHeadTranslationDefect_log_bound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (L : {L : ℝ // 0 < L})
    (h : {h : ℝ // 0 < h ∧ 2 * h < (L : ℝ)}) :
    Real.log ((L : ℝ) / (2 * (h : ℝ))) *
        ccmActualHeadTranslationDefect h
          (ccmArchimedeanFormToAperture a u : SoninL2) ≤
      8 * Real.exp (5 * (L : ℝ) / 2) *
        ccmActualHeadGammaHigherBinetModeEnergy
          (ccmArchimedeanFormToAperture a u : SoninL2) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let G : ℝ → ℝ := fun s =>
    ccmGammaHigherBinetModeDensity s * ccmActualHeadTranslationDefect s f
  have hE (s : ℝ) : 0 ≤ ccmActualHeadTranslationDefect s f := by
    unfold ccmActualHeadTranslationDefect
    positivity
  have hGint : IntegrableOn G (Ioi (0 : ℝ)) :=
    integrableOn_ccmGammaHigherBinetModeDensity_mul_translationDefect_formDomain a u
  have hGae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (ccmGammaHigherBinetModeDensity_pos hs).le (hE s)
  have hGI (r b : ℝ) (hr : 0 < r) (hrb : r ≤ b) :
      IntervalIntegrable G volume r b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hrb).mpr
    exact hGint.mono_set (by intro s hs; exact hr.trans_le hs.1)
  have hGB (r b : ℝ) (hr : 0 ≤ r) (hrb : r ≤ b) :
      (∫ s in r..b, G s) ≤ ccmActualHeadGammaHigherBinetModeEnergy f := by
    rw [ccmActualHeadGammaHigherBinetModeEnergy_eq_integral_formDomain a u,
      intervalIntegral.integral_of_le hrb]
    exact setIntegral_mono_set hGint hGae
      (show Ioc r b ⊆ Ioi (0 : ℝ) from
        fun s hs => hr.trans_lt hs.1).eventuallyLE
  have hab : 2 * (h : ℝ) ≤ (L : ℝ) := h.property.2.le
  have hshift : IntervalIntegrable (fun s => G (s - (h : ℝ))) volume
      (2 * (h : ℝ)) (L : ℝ) := by
    simpa only [sub_add_cancel] using
      (hGI (2 * (h : ℝ) - (h : ℝ)) ((L : ℝ) - (h : ℝ))
        (by linarith [h.property.1]) (by linarith)).comp_sub_right (h : ℝ)
  have hinv : IntervalIntegrable (fun s : ℝ => 1 / s) volume
      (2 * (h : ℝ)) (L : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_const.div continuousOn_id
      (by intro s hs; exact ne_of_gt (by linarith [h.property.1, hs.1]))
  have hpoint (s : ℝ) (hs : s ∈ Icc (2 * (h : ℝ)) (L : ℝ)) :
      (1 / s) * ccmActualHeadTranslationDefect h f ≤
        (4 * Real.exp (5 * (L : ℝ) / 2)) * (G s + G (s - (h : ℝ))) := by
    have hspos : 0 < s := by linarith [h.property.1, hs.1]
    have hdpos : 0 < s - (h : ℝ) := by linarith [h.property.1, hs.1]
    have hds : s - (h : ℝ) ≤ s := by linarith [h.property.1]
    have h₁ := mul_le_mul_of_nonneg_right
      (one_div_le_ccmGammaHigherBinetModeDensity L ⟨s, hspos, hs.2⟩) (hE s)
    have h₂ := mul_le_mul_of_nonneg_right
      ((one_div_le_one_div_of_le hdpos hds).trans
        (one_div_le_ccmGammaHigherBinetModeDensity L
          ⟨s - (h : ℝ), hdpos, hds.trans hs.2⟩)) (hE (s - (h : ℝ)))
    have htri := mul_le_mul_of_nonneg_left
      (ccmActualHeadTranslationDefect_le_two_add h s f) (by positivity : 0 ≤ 1 / s)
    dsimp only [G]
    nlinarith only [h₁, h₂, htri]
  have hmono := intervalIntegral.integral_mono_on hab
    (hinv.mul_const (ccmActualHeadTranslationDefect h f))
    (((hGI (2 * (h : ℝ)) L (by linarith [h.property.1]) hab).add hshift).const_mul
      (4 * Real.exp (5 * (L : ℝ) / 2))) hpoint
  rw [intervalIntegral.integral_mul_const,
    integral_one_div_of_pos (by linarith [h.property.1]) L.property,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      (hGI (2 * (h : ℝ)) L (by linarith [h.property.1]) hab) hshift,
    intervalIntegral.integral_comp_sub_right] at hmono
  have hB₁ := hGB (2 * (h : ℝ)) L (by linarith [h.property.1]) hab
  have hB₂ := hGB (2 * (h : ℝ) - (h : ℝ)) ((L : ℝ) - (h : ℝ))
    (by linarith [h.property.1]) (by linarith)
  have hexp : 0 ≤ Real.exp (5 * (L : ℝ) / 2) := (Real.exp_pos _).le
  change _ ≤ 8 * Real.exp (5 * (L : ℝ) / 2) *
    ccmActualHeadGammaHigherBinetModeEnergy f
  nlinarith only [hmono, mul_le_mul_of_nonneg_left hB₁ hexp,
    mul_le_mul_of_nonneg_left hB₂ hexp]

end RHTower
