import GaloisForLFunctions.RHTower.CCMCoherentMidpointSpectralCurrent
import GaloisForLFunctions.RHTower.CCMCoherentMidpointGammaReduction

/-!
# Spectral form of the actual midpoint action and Gamma square

The increment and the arithmetic odd field have the same midpoint phase.
Their interference is therefore one real scalar square, before integration.
The resulting source identity retains the signed current rather than bounding
the prime and terminal contributions separately.
-/

noncomputable section
open Complex MeasureTheory
open scoped InnerProduct BigOperators

namespace RHTower

private theorem combination_fourier_ae (T : ℝ) (N : ℕ) (f : SoninL2) (r a b : ℝ) :
    (fourierUnitary ((a : ℂ) • (logTranslationCLM r f-f) +
      (b : ℂ) • ccmActualHeadMidpointOddField T N f r) : ℝ → ℂ) =ᵐ[volume]
    fun ξ => (Complex.I * MellinL2.fourierPhase (r/2) ξ *
      ((2*a*Real.sin (Real.pi*r*ξ)-b*ccmActualHeadMidpointSineSymbol T N r ξ : ℝ) : ℂ)) *
        fourierUnitary f ξ := by
  rw [map_add, map_smul, map_smul]
  filter_upwards [Lp.coeFn_add
      ((a : ℂ) • fourierUnitary (logTranslationCLM r f-f))
      ((b : ℂ) • fourierUnitary (ccmActualHeadMidpointOddField T N f r)),
    Lp.coeFn_smul (a : ℂ) (fourierUnitary (logTranslationCLM r f-f)),
    Lp.coeFn_smul (b : ℂ) (fourierUnitary (ccmActualHeadMidpointOddField T N f r)),
    fourier_logTranslation_increment_ae r f,
    fourier_ccmActualHeadMidpointOddField_ae T N f r] with ξ ha h₁ h₂ hδ hO
  rw [ha, Pi.add_apply, h₁, h₂, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hδ, hO]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The exact real spectral square of an increment plus its arithmetic odd field. -/
theorem norm_sq_increment_add_midpointOdd_eq_spectral (T : ℝ) (N : ℕ)
    (f : SoninL2) (r a b : ℝ) :
    ‖(a : ℂ) • (logTranslationCLM r f-f) +
      (b : ℂ) • ccmActualHeadMidpointOddField T N f r‖^2 =
    ∫ ξ : ℝ, (2*a*Real.sin (Real.pi*r*ξ)-b*ccmActualHeadMidpointSineSymbol T N r ξ)^2 *
      ‖fourierUnitary f ξ‖^2 := by
  rw [← fourierUnitary.norm_map ((a : ℂ) • (logTranslationCLM r f-f) +
      (b : ℂ) • ccmActualHeadMidpointOddField T N f r), norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [combination_fourier_ae T N f r a b] with ξ hξ
  rw [hξ]
  simp only [norm_mul, Complex.norm_I, MellinL2.norm_fourierPhase,
    Complex.norm_real, Real.norm_eq_abs, one_mul, mul_pow, sq_abs]

/-- The odd Gamma cost is precisely the reciprocal-Gamma-weighted spectral sine energy. -/
theorem ccmActualHeadMidpointOddGammaCost_eq_spectral (T : ℝ) (N : ℕ) (f : SoninL2) :
    ccmActualHeadMidpointOddGammaCost T N f =
      ∫ r : ℝ, (∫ ξ : ℝ,
        (ccmActualHeadMidpointSineSymbol T N r ξ)^2 * ‖fourierUnitary f ξ‖^2) *
          ccmGammaHigherBinetDualDensity |r| := by
  simp only [ccmActualHeadMidpointOddGammaCost, norm_sq_ccmActualHeadMidpointOddField_eq_spectral]

/-- The full Gamma square keeps the arithmetic sum inside the scalar square. -/
theorem ccmActualHeadMidpointOddGammaSquare_eq_spectral (T : ℝ) (N : ℕ) (f : SoninL2) :
    ccmActualHeadMidpointOddGammaSquare T N f =
      ∫ r : ℝ, ∫ ξ : ℝ,
        (2*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)*Real.sin (Real.pi*r*ξ) -
          Real.sqrt (ccmGammaHigherBinetDualDensity |r|)*ccmActualHeadMidpointSineSymbol T N r ξ)^2 *
            ‖fourierUnitary f ξ‖^2 := by
  simp only [ccmActualHeadMidpointOddGammaSquare, norm_sq_increment_add_midpointOdd_eq_spectral]

/-- The completed current has an exact iterated spectral integral; no exchange of integrals is used. -/
theorem ccmActualHeadCompletedQuantileCurrent_eq_midpoint_spectral
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadCompletedQuantileCurrent a f =
      ∫ r : ℝ, ∫ ξ : ℝ,
        ccmActualHeadMidpointCurrentSymbol (2*a.1) (Nat.floor (Real.exp (2*a.1))+1) r ξ *
          ‖fourierUnitary f.1 ξ‖^2 := by
  have h := ccmActualHeadCompletedQuantileCurrent_eq_integral_coherentField a f
  change ccmActualHeadCompletedQuantileCurrent a f =
    ∫ r : ℝ, (inner ℂ (logTranslationCLM r f.1-f.1)
      (ccmActualHeadQuantileCompletedCoherentField (2*a.1)
        (Nat.floor (Real.exp (2*a.1))+1) f.1 r)).re at h
  rw [h]
  apply integral_congr_ae
  filter_upwards with r
  exact re_inner_increment_completed_eq_midpoint_spectral _ _ _ _

/-- The original Weil source in terms of the exact signed spectral current. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_midpoint_spectral_current
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    ccmRestrictedWeilSourceQuadratic a u =
      (2*gammaHardyPhaseRate 0+4)*‖f‖^2 + ccmActualHeadGammaHigherBinetModeEnergy f.1 +
        2*(∫ r : ℝ, ∫ ξ : ℝ,
          ccmActualHeadMidpointCurrentSymbol (2*a.1) (Nat.floor (Real.exp (2*a.1))+1) r ξ *
            ‖fourierUnitary f.1 ξ‖^2) := by
  have h := ccmRestrictedWeilSourceQuadratic_eq_midpointGaugeAction a u 0
  have hi := integral_ccmActualHeadMidpointGaugeAction a u 0
  dsimp only at h hi ⊢
  rw [hi, ccmActualHeadCompletedQuantileCurrent_eq_midpoint_spectral] at h
  linarith only [h]

end RHTower
