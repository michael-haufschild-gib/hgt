import GaloisForLFunctions.RHTower.CCM.CCMCoherentMidpointMomentGauge
import GaloisForLFunctions.RHTower.CCM.CCMGammaCurrentActionDuality

/-!
# The moment-cancelling correction is an actual field symmetry

The exterior sine correction comes from a literal pair of translated `L²`
fields. Its real current vanishes on the physical aperture, so every real
multiple preserves the Gamma action. The distinguished multiple removes the
first frequency moment and realizes the quartic spectral representative.
-/

noncomputable section
open Complex MeasureTheory
open scoped InnerProduct BigOperators

namespace RHTower

def ccmMidpointExteriorOddField (a : SuzukiPositiveAperture) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ((1/2 : ℝ) : ℂ) • (logTranslationCLM (-ccmMidpointExteriorShift a r) f -
    logTranslationCLM (r+ccmMidpointExteriorShift a r) f)

theorem fourier_ccmMidpointExteriorOddField_ae (a : SuzukiPositiveAperture)
    (f : SoninL2) (r : ℝ) :
    (fourierUnitary (ccmMidpointExteriorOddField a f r) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (-Complex.I*MellinL2.fourierPhase (r/2) ξ *
        (Real.sin (ccmMidpointExteriorFrequency a r*ξ) : ℂ))*fourierUnitary f ξ := by
  have h := fourier_midpointOdd_translation_packet_ae ({()} : Finset Unit)
    (fun _ => 1) (fun _ => ccmMidpointExteriorShift a r) r f
  simpa only [Finset.sum_singleton, Complex.ofReal_one, one_smul, one_mul,
    ccmMidpointExteriorOddField, ccmMidpointExteriorFrequency] using h

/-- Physical support makes the exterior pair invisible to the signed current. -/
theorem re_inner_increment_ccmMidpointExteriorOddField_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f.1-f.1) (ccmMidpointExteriorOddField a f.1 r)).re = 0 := by
  have hshift := ccmActualHeadAutocorrelation_add_sub_eq_re_inner_increment_shifted
    r (ccmMidpointExteriorShift a r) f.1
  rw [ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le a f
      (ccmMidpointExteriorShift_ge a r).2,
    ccmActualHeadSymmetricAutocorrelation_eq_zero_of_two_aperture_le a f
      (ccmMidpointExteriorShift_ge a r).1, sub_self] at hshift
  have hsum := re_inner_increment_reflected_shift_sum_zero r (ccmMidpointExteriorShift a r) f.1
  rw [inner_add_right, Complex.add_re] at hsum
  simp only [ccmMidpointExteriorOddField, inner_smul_right, inner_sub_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
  linarith only [hshift, hsum]

/-- An explicit continuous field-translation symmetry of the actual Gamma action. -/
theorem ccmGammaIncrementAction_exteriorOdd_invariant
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (v : SoninL2) (r θ : ℝ) :
    ccmGammaIncrementAction f.1 r (v+(θ : ℂ) • ccmMidpointExteriorOddField a f.1 r) =
      ccmGammaIncrementAction f.1 r v :=
  (ccmGammaIncrementAction_translation_invariant_iff f.1 v
    (ccmMidpointExteriorOddField a f.1 r) r).mpr
      (re_inner_increment_ccmMidpointExteriorOddField_zero a f r) θ

theorem hasDerivAt_ccmGammaIncrementAction_exteriorOdd_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (v : SoninL2) (r θ : ℝ) :
    HasDerivAt (fun η : ℝ => ccmGammaIncrementAction f.1 r
      (v+(η : ℂ) • ccmMidpointExteriorOddField a f.1 r)) 0 θ := by
  simpa only [re_inner_increment_ccmMidpointExteriorOddField_zero, mul_zero] using
    hasDerivAt_ccmGammaIncrementAction_add_real_smul f.1 v
      (ccmMidpointExteriorOddField a f.1 r) r θ

def ccmActualHeadMomentCancelledField (a : SuzukiPositiveAperture) (N : ℕ)
    (f : SoninL2) (r : ℝ) : SoninL2 :=
  ccmActualHeadMidpointOddField (2*a.1) N f r -
    ((ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequency a r : ℝ) : ℂ) •
      ccmMidpointExteriorOddField a f r

/-- The quartic spectral representative is the Fourier transform of a literal corrected field. -/
theorem fourier_ccmActualHeadMomentCancelledField_ae (a : SuzukiPositiveAperture)
    (N : ℕ) (f : SoninL2) (r : ℝ) :
    (fourierUnitary (ccmActualHeadMomentCancelledField a N f r) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (-Complex.I*MellinL2.fourierPhase (r/2) ξ *
        (ccmActualHeadMomentCancelledSine a N r ξ : ℂ))*fourierUnitary f ξ := by
  let c : ℂ := (ccmActualHeadMidpointSignedMoment (2*a.1) N r/ccmMidpointExteriorFrequency a r : ℝ)
  change (fourierUnitary (ccmActualHeadMidpointOddField (2*a.1) N f r -
    c • ccmMidpointExteriorOddField a f r) : ℝ → ℂ) =ᵐ[volume] _
  rw [map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (fourierUnitary (ccmActualHeadMidpointOddField (2*a.1) N f r))
      (c • fourierUnitary (ccmMidpointExteriorOddField a f r)),
    Lp.coeFn_smul c (fourierUnitary (ccmMidpointExteriorOddField a f r)),
    fourier_ccmActualHeadMidpointOddField_ae (2*a.1) N f r,
    fourier_ccmMidpointExteriorOddField_ae a f r] with ξ hs hc hO hE
  rw [hs, Pi.sub_apply, hc, Pi.smul_apply, smul_eq_mul, hO, hE]
  simp only [ccmActualHeadMomentCancelledSine, Complex.ofReal_sub, Complex.ofReal_mul, c]
  ring

/-- Current conservation holds directly in the physical Hilbert space. -/
theorem re_inner_increment_momentCancelledField (a : SuzukiPositiveAperture)
    (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f.1-f.1) (ccmActualHeadMomentCancelledField a N f.1 r)).re =
      (inner ℂ (logTranslationCLM r f.1-f.1)
        (ccmActualHeadQuantileCompletedCoherentField (2*a.1) N f.1 r)).re := by
  rw [ccmActualHeadMomentCancelledField, inner_sub_right, Complex.sub_re,
    inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, re_inner_increment_ccmMidpointExteriorOddField_zero, mul_zero, sub_zero,
    re_inner_increment_midpointOdd]

/-- Cancelling the first moment changes neither the original action nor the exact current. -/
theorem ccmGammaIncrementAction_momentCancelledField (a : SuzukiPositiveAperture)
    (N : ℕ) (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmGammaIncrementAction f.1 r (ccmActualHeadMomentCancelledField a N f.1 r) =
      ccmGammaIncrementAction f.1 r (ccmActualHeadMidpointOddField (2*a.1) N f.1 r) := by
  apply (ccmGammaIncrementAction_eq_iff_current_eq _ _ _ _).mpr
  rw [re_inner_increment_momentCancelledField, re_inner_increment_midpointOdd]

/-- The corrected field energy keeps its complete signed spectral amplitude inside the square. -/
theorem norm_sq_ccmActualHeadMomentCancelledField_eq_spectral
    (a : SuzukiPositiveAperture) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadMomentCancelledField a N f r‖^2 =
      ∫ ξ : ℝ, (ccmActualHeadMomentCancelledSine a N r ξ)^2*‖fourierUnitary f ξ‖^2 := by
  rw [← fourierUnitary.norm_map (ccmActualHeadMomentCancelledField a N f r), norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [fourier_ccmActualHeadMomentCancelledField_ae a N f r] with ξ hξ
  rw [hξ]
  simp only [norm_mul, norm_neg, Complex.norm_I, MellinL2.norm_fourierPhase,
    Complex.norm_real, Real.norm_eq_abs, one_mul, mul_pow, sq_abs]

end RHTower
