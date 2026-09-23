import GaloisForLFunctions.HTGeometry.CoulombGammaPhaseClock

/-!
# Reflected-frequency observability for moving-center Gamma clocks

Black-hole Coulomb-wave asymptotics can contain a Gamma phase whose center is not constant but an
even algebraic function of frequency.  Appendix B of K. K. Ng, C. Zhang, J. Louko, and R. B. Mann,
*A Little Excitement Across the Horizon*, arXiv:2109.13260, uses

`Gamma(nu_a(omega)+1+i*eta) / Gamma(nu_a(omega)+1-i*eta)`

with `eta=-2*M*omega` and

`nu_a(omega)=(-1+sqrt((2*ell+1)^(2 : ℕ)-12*(2*M*omega)^(2 : ℕ)))/2`.

The present meromorphic orbit-charge classifier only handles constant affine Gamma centers, so it
does not yet classify the differential algebraicity of this moving-center carrier.  The exact
observation algebra nevertheless needs no such classifier: every even center makes frequency
reflection reciprocal, reflected-frequency intensity unit, and the orientation observation the
square of the original carrier wherever the two Gamma values are nonzero.

This establishes a useful boundary beyond the current HT theorem: intensity blindness is stable
under arbitrary even motion of the Gamma center and is not an artifact of fixed shifts.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Gamma scattering carrier with an arbitrary frequency-dependent center. -/
def movingCenterGammaCarrierValue
    (center : ℂ → ℂ) (scale omega : ℂ) : ℂ :=
  Complex.Gamma (center omega + Complex.I * scale * omega) /
    Complex.Gamma (center omega - Complex.I * scale * omega)

/-- Reflected-frequency intensity of a moving-center Gamma carrier. -/
def movingCenterGammaIntensityValue
    (center : ℂ → ℂ) (scale omega : ℂ) : ℂ :=
  movingCenterGammaCarrierValue center scale omega *
    movingCenterGammaCarrierValue center scale (-omega)

/-- Orientation-sensitive quotient of a moving-center Gamma carrier. -/
def movingCenterGammaOrientationValue
    (center : ℂ → ℂ) (scale omega : ℂ) : ℂ :=
  movingCenterGammaCarrierValue center scale omega /
    movingCenterGammaCarrierValue center scale (-omega)

/-- **Moving-center reflection law.**  An even center makes the frequency-reflected carrier the
reciprocal of the original carrier away from Gamma poles. -/
theorem movingCenterGammaCarrierValue_neg
    (center : ℂ → ℂ) (scale omega : ℂ)
    (hcenter : center (-omega) = center omega)
    (hplus : Complex.Gamma
      (center omega + Complex.I * scale * omega) ≠ 0)
    (hminus : Complex.Gamma
      (center omega - Complex.I * scale * omega) ≠ 0) :
    movingCenterGammaCarrierValue center scale (-omega) =
      (movingCenterGammaCarrierValue center scale omega)⁻¹ := by
  unfold movingCenterGammaCarrierValue
  rw [hcenter]
  have hargPlus :
      center omega + Complex.I * scale * (-omega) =
        center omega - Complex.I * scale * omega := by ring
  have hargMinus :
      center omega - Complex.I * scale * (-omega) =
        center omega + Complex.I * scale * omega := by ring
  rw [hargPlus, hargMinus]
  field_simp [hplus, hminus]

/-- **Moving-center intensity collapse.**  Every even moving center has unit reflected-frequency
intensity away from Gamma poles. -/
theorem movingCenterGammaIntensityValue_eq_one
    (center : ℂ → ℂ) (scale omega : ℂ)
    (hcenter : center (-omega) = center omega)
    (hplus : Complex.Gamma
      (center omega + Complex.I * scale * omega) ≠ 0)
    (hminus : Complex.Gamma
      (center omega - Complex.I * scale * omega) ≠ 0) :
    movingCenterGammaIntensityValue center scale omega = 1 := by
  rw [movingCenterGammaIntensityValue,
    movingCenterGammaCarrierValue_neg center scale omega hcenter hplus hminus]
  apply mul_inv_cancel₀
  exact div_ne_zero hplus hminus

/-- **Moving-center orientation value relation.**  The orientation observation retains the square
of the carrier even when intensity is unit. -/
theorem movingCenterGammaOrientationValue_eq_square
    (center : ℂ → ℂ) (scale omega : ℂ)
    (hcenter : center (-omega) = center omega)
    (hplus : Complex.Gamma
      (center omega + Complex.I * scale * omega) ≠ 0)
    (hminus : Complex.Gamma
      (center omega - Complex.I * scale * omega) ≠ 0) :
    movingCenterGammaOrientationValue center scale omega =
      (movingCenterGammaCarrierValue center scale omega) ^ (2 : ℕ) := by
  rw [movingCenterGammaOrientationValue,
    movingCenterGammaCarrierValue_neg center scale omega hcenter hplus hminus]
  field_simp [div_ne_zero hplus hminus]

/-- Algebraically moving angular center used in the Schwarzschild detector Coulomb-wave
asymptotics.  `massFrequencyScale` represents `2*M`. -/
def schwarzschildDetectorRenormalizedAngularCenter
    (ell : ℕ) (massFrequencyScale omega : ℂ) : ℂ :=
  (-1 + Complex.sqrt
    ((((2 * ell + 1 : ℕ) : ℂ) ^ (2 : ℕ)) -
      12 * (massFrequencyScale * omega) ^ (2 : ℕ))) / 2

/-- The Schwarzschild detector's renormalized angular center is even in frequency. -/
theorem schwarzschildDetectorRenormalizedAngularCenter_neg
    (ell : ℕ) (massFrequencyScale omega : ℂ) :
    schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale (-omega) =
      schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale omega := by
  unfold schwarzschildDetectorRenormalizedAngularCenter
  congr 3
  ring

/-- Gamma ratio underlying the Coulomb phase in the Schwarzschild detector mode estimate. -/
def schwarzschildDetectorCoulombGammaCarrierValue
    (ell : ℕ) (massFrequencyScale omega : ℂ) : ℂ :=
  movingCenterGammaCarrierValue
    (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale)
    (-massFrequencyScale) omega

/-- The Schwarzschild moving-center carrier has unit reflected-frequency intensity wherever its
two Gamma values are nonzero. -/
theorem schwarzschildDetectorCoulombGammaIntensityValue_eq_one
    (ell : ℕ) (massFrequencyScale omega : ℂ)
    (hplus : Complex.Gamma
      (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale omega +
        Complex.I * (-massFrequencyScale) * omega) ≠ 0)
    (hminus : Complex.Gamma
      (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale omega -
        Complex.I * (-massFrequencyScale) * omega) ≠ 0) :
    movingCenterGammaIntensityValue
        (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale)
        (-massFrequencyScale) omega = 1 := by
  exact movingCenterGammaIntensityValue_eq_one _ _ _
    (schwarzschildDetectorRenormalizedAngularCenter_neg
      ell massFrequencyScale omega) hplus hminus

/-- The corresponding orientation observation is exactly the square of the Schwarzschild
moving-center Gamma carrier. -/
theorem schwarzschildDetectorCoulombGammaOrientationValue_eq_square
    (ell : ℕ) (massFrequencyScale omega : ℂ)
    (hplus : Complex.Gamma
      (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale omega +
        Complex.I * (-massFrequencyScale) * omega) ≠ 0)
    (hminus : Complex.Gamma
      (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale omega -
        Complex.I * (-massFrequencyScale) * omega) ≠ 0) :
    movingCenterGammaOrientationValue
        (schwarzschildDetectorRenormalizedAngularCenter ell massFrequencyScale)
        (-massFrequencyScale) omega =
      (schwarzschildDetectorCoulombGammaCarrierValue
        ell massFrequencyScale omega) ^ (2 : ℕ) := by
  exact movingCenterGammaOrientationValue_eq_square _ _ _
    (schwarzschildDetectorRenormalizedAngularCenter_neg
      ell massFrequencyScale omega) hplus hminus

end


end GaloisForLFunctions.HTGeometry
