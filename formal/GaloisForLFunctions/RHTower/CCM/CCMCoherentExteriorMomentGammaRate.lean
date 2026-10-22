import GaloisForLFunctions.RHTower.CCM.CCMCoherentExteriorMomentGammaLimit

/-!
# Exact Gamma asymptotic of the exterior moment correction

The inverse-square estimate has an exact leading coefficient: after multiplying
by `(2π(n+1))²`, the correction cost converges to half the source norm squared
times the weighted energy of the literal arithmetic moment. The domination is
uniform in displacement; aperture and arithmetic cutoff remain fixed.
-/

noncomputable section
open MeasureTheory Filter Topology

namespace RHTower

def ccmMidpointExteriorFrequencyFraction (a : SuzukiPositiveAperture) (r : ℝ) (n : ℕ) : ℝ :=
  (2*Real.pi*((n : ℝ)+1))/ccmMidpointExteriorFrequencyAt a r n

theorem ccmMidpointExteriorFrequencyFraction_mem_Icc (a : SuzukiPositiveAperture)
    (r : ℝ) (n : ℕ) : ccmMidpointExteriorFrequencyFraction a r n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (by positivity) (ccmMidpointExteriorFrequencyAt_pos a r n).le
  · exact (div_le_one (ccmMidpointExteriorFrequencyAt_pos a r n)).mpr
      (ccmMidpointExteriorFrequencyAt_lower a r n)

theorem tendsto_ccmMidpointExteriorFrequencyFraction (a : SuzukiPositiveAperture) (r : ℝ) :
    Tendsto (ccmMidpointExteriorFrequencyFraction a r) atTop (𝓝 1) := by
  have he : ccmMidpointExteriorFrequencyFraction a r = fun n : ℕ =>
      1-(ccmMidpointExteriorFrequency a r-2*Real.pi)/ccmMidpointExteriorFrequencyAt a r n := by
    funext n
    unfold ccmMidpointExteriorFrequencyFraction
    have hβ := ne_of_gt (ccmMidpointExteriorFrequencyAt_pos a r n)
    field_simp [hβ]
    rw [ccmMidpointExteriorFrequencyAt_eq]
    ring
  rw [he]
  have h : Tendsto (fun n => (ccmMidpointExteriorFrequency a r-2*Real.pi)/
      ccmMidpointExteriorFrequencyAt a r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_ccmMidpointExteriorFrequencyAt a r)
  simpa only [sub_zero] using tendsto_const_nhds.sub h

private theorem normalized_density (a : SuzukiPositiveAperture) (N : ℕ)
    (f : suzukiApertureHilbert a) (n : ℕ) (r : ℝ) :
    (2*Real.pi*((n : ℝ)+1))^2 *
        (‖ccmActualHeadMomentCorrectionAt a N f.1 r n‖^2 * ccmGammaHigherBinetDualDensity |r|) =
      (‖f.1‖^2/2) * ((ccmMidpointExteriorFrequencyFraction a r n)^2 *
        ((ccmActualHeadMidpointSignedMoment (2*a.1) N r)^2 * ccmGammaHigherBinetDualDensity |r|)) := by
  rw [norm_sq_ccmActualHeadMomentCorrectionAt]
  unfold ccmMidpointExteriorFrequencyFraction
  simp only [div_pow]
  ring

/-- The inverse-square decay coefficient retains the full signed arithmetic moment. -/
theorem tendsto_ccmActualHeadMomentCorrectionGammaCost_scaled (a : SuzukiPositiveAperture)
    (N : ℕ) (f : suzukiApertureHilbert a) :
    Tendsto (fun n : ℕ => (2*Real.pi*((n : ℝ)+1))^2 *
      ccmActualHeadMomentCorrectionGammaCost a N f.1 n) atTop
      (𝓝 ((‖f.1‖^2/2)*ccmActualHeadSignedMomentGammaEnergy (2*a.1) N)) := by
  let D := fun r : ℝ => (ccmActualHeadMidpointSignedMoment (2*a.1) N r)^2 *
    ccmGammaHigherBinetDualDensity |r|
  have hD : Integrable D := integrable_ccmActualHeadSignedMomentGammaDensity (2*a.1) N
  have hD0 (r : ℝ) : 0 ≤ D r :=
    mul_nonneg (sq_nonneg _) (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))
  have ht : Tendsto (fun n => ∫ r : ℝ, (ccmMidpointExteriorFrequencyFraction a r n)^2 * D r)
      atTop (𝓝 (∫ r : ℝ, D r)) := by
    apply tendsto_integral_of_dominated_convergence D
    · intro n
      have hm : Measurable (fun r : ℝ => (ccmMidpointExteriorFrequencyFraction a r n)^2) := by
        unfold ccmMidpointExteriorFrequencyFraction ccmMidpointExteriorFrequencyAt
          ccmMidpointExteriorShiftAt ccmMidpointExteriorShift
        fun_prop
      exact hm.aestronglyMeasurable.mul hD.aestronglyMeasurable
    · exact hD
    · intro n
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hD0 r))]
      have hq := ccmMidpointExteriorFrequencyFraction_mem_Icc a r n
      have hq2 : (ccmMidpointExteriorFrequencyFraction a r n)^2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ hq.1 hq.2 2
      exact (mul_le_mul_of_nonneg_right hq2 (hD0 r)).trans_eq (one_mul _)
    · filter_upwards with r
      simpa only [one_pow, one_mul] using
        ((tendsto_ccmMidpointExteriorFrequencyFraction a r).pow 2).mul_const (D r)
  have he (n : ℕ) : (2*Real.pi*((n : ℝ)+1))^2 *
      ccmActualHeadMomentCorrectionGammaCost a N f.1 n =
      (‖f.1‖^2/2)*(∫ r : ℝ, (ccmMidpointExteriorFrequencyFraction a r n)^2 * D r) := by
    rw [ccmActualHeadMomentCorrectionGammaCost, ← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (normalized_density a N f n))
  simp_rw [he]
  exact ht.const_mul _

end RHTower
