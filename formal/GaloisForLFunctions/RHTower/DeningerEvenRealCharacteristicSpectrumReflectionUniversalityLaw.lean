import GaloisForLFunctions.RHTower.DeningerArithmeticCharacteristic
import GaloisForLFunctions.RHTower.DeningerArithmeticRealStructure

/-!
# Deninger even-Real characteristic-spectrum reflection universality

The functional-equation Real involution simultaneously reflects the centered source
characteristic and transports every quotient-Frobenius eigenvector.  Thus source zeros and
point-spectrum fibres carry the same involutive reflection.
-/

open Complex

namespace RHTower

noncomputable section

/-- Functional-equation reflection of the centered spectral parameter. -/
def deningerCenteredSpectralReflection (alpha : ℂ) : ℂ :=
  -(starRingEnd ℂ) alpha

@[simp]
theorem deningerCenteredSpectralReflection_involutive (alpha : ℂ) :
    deningerCenteredSpectralReflection
        (deningerCenteredSpectralReflection alpha) = alpha := by
  simp [deningerCenteredSpectralReflection]

/-- The centered source characteristic has an invariant zero set under the even-Real spectral
reflection. -/
theorem deningerArithmeticH1CenteredCharacteristic_reflection (alpha : ℂ) :
    deningerArithmeticH1CenteredCharacteristic
        (deningerCenteredSpectralReflection alpha) = 0 ↔
      deningerArithmeticH1CenteredCharacteristic alpha = 0 := by
  have hfix := congrArg
    (fun F : DeningerEntire => F alpha)
    deningerEntireFunctionalEquationSigma_Xi
  change
    (starRingEnd ℂ)
        (XiC (deningerCenteredSpectralReflection alpha)) = XiC alpha at hfix
  rw [← deningerArithmeticH1CenteredCharacteristic_eq,
    ← deningerArithmeticH1CenteredCharacteristic_eq] at hfix
  constructor
  · intro hreflect
    rw [hreflect, map_zero] at hfix
    exact hfix.symm
  · intro halpha
    rw [halpha] at hfix
    have hconj := congrArg (starRingEnd ℂ) hfix
    simpa using hconj

/-- The descended even-Real involution maps every nonzero Frobenius eigenvector to the reflected
nonzero eigenspace. -/
theorem deningerArithmeticH1EvenKReal_sigma_eigenvector
    {alpha : ℂ} {x : DeningerArithmeticH1}
    (hx0 : x ≠ 0)
    (hx : deningerEntireTheta x = (1 / 2 + I * alpha) • x) :
    deningerArithmeticH1EvenKReal.sigma x ≠ 0 ∧
      deningerEntireTheta (deningerArithmeticH1EvenKReal.sigma x) =
        (1 / 2 + I * deningerCenteredSpectralReflection alpha) •
          deningerArithmeticH1EvenKReal.sigma x := by
  constructor
  · intro hsigma
    have hsq :
        deningerArithmeticH1EvenKReal.sigma
            (deningerArithmeticH1EvenKReal.sigma x) = x := by
      simpa [GaloisForLFunctions.RHTower.kRealParityAction] using
        deningerArithmeticH1EvenKReal.sq x
    rw [hsigma, map_zero] at hsq
    exact hx0 hsq.symm
  · calc
      deningerEntireTheta (deningerArithmeticH1EvenKReal.sigma x) =
          deningerArithmeticH1EvenKReal.sigma (deningerEntireTheta x) :=
        (deningerArithmeticH1EvenKReal_commutes_theta x).symm
      _ = deningerArithmeticH1EvenKReal.sigma
          ((1 / 2 + I * alpha) • x) := by rw [hx]
      _ = (starRingEnd ℂ) (1 / 2 + I * alpha) •
          deningerArithmeticH1EvenKReal.sigma x := by
            rw [map_smulₛₗ]
      _ = (1 / 2 + I * deningerCenteredSpectralReflection alpha) •
          deningerArithmeticH1EvenKReal.sigma x := by
            congr 1
            simp [deningerCenteredSpectralReflection, map_ofNat]

/-- **Deninger even-Real characteristic-spectrum reflection universality law.**  The same
involutive centered reflection preserves the source-characteristic zero set and transports every
nonzero quotient-Frobenius eigenvector to its reflected eigenvalue. -/
theorem deninger_evenReal_characteristicSpectrumReflectionUniversality
    (alpha : ℂ) :
    deningerCenteredSpectralReflection
        (deningerCenteredSpectralReflection alpha) = alpha ∧
    (deningerArithmeticH1CenteredCharacteristic alpha = 0 ↔
      deningerArithmeticH1CenteredCharacteristic
        (deningerCenteredSpectralReflection alpha) = 0) ∧
    ∀ x : DeningerArithmeticH1,
      x ≠ 0 →
      deningerEntireTheta x = (1 / 2 + I * alpha) • x →
      deningerArithmeticH1EvenKReal.sigma x ≠ 0 ∧
        deningerEntireTheta (deningerArithmeticH1EvenKReal.sigma x) =
          (1 / 2 + I * deningerCenteredSpectralReflection alpha) •
            deningerArithmeticH1EvenKReal.sigma x := by
  exact ⟨deningerCenteredSpectralReflection_involutive alpha,
    (deningerArithmeticH1CenteredCharacteristic_reflection alpha).symm,
      fun _ hx0 hx =>
        deningerArithmeticH1EvenKReal_sigma_eigenvector hx0 hx⟩

end

end RHTower
