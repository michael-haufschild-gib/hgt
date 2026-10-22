import GaloisForLFunctions.RHTower.CCM.CCMThetaSignedLocalizationWitness

/-!
# An exact arithmetic phase orbit

For an angle taking only zero and pi on the physical support, every link
error scales by `(1-cos(t))/2` when the angle is multiplied by `t/pi`.
The actual separated-source witnesses therefore have a nonconstant phase
energy `Q(u)+B(1-cos(t))`, with B strictly positive and every prime error zero.
This is a literal arithmetic potential, not a chosen model for the error.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def ccmScaledPhaseAngle (theta : 𝓢(ℝ, ℝ)) (t : ℝ) : 𝓢(ℝ, ℝ) :=
  (t / Real.pi) • theta

@[simp] theorem ccmScaledPhaseAngle_apply (theta : 𝓢(ℝ, ℝ)) (t x : ℝ) :
    ccmScaledPhaseAngle theta t x = t / Real.pi * theta x := rfl

def ccmPhaseLocalizationEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (t : ℝ) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a (ccmCosLocalizedSource u (ccmScaledPhaseAngle theta t)).toCCMFormVector +
    ccmRestrictedWeilSourceQuadratic a (ccmSinLocalizedSource u (ccmScaledPhaseAngle theta t)).toCCMFormVector

theorem thetaLocalizationWeight_scaledPhase (theta : 𝓢(ℝ, ℝ)) (t x y : ℝ)
    (hx : theta x = 0 ∨ theta x = Real.pi) (hy : theta y = 0 ∨ theta y = Real.pi) :
    thetaLocalizationWeight (ccmScaledPhaseAngle theta t) x y =
      ((1 - Real.cos t) / 2) * thetaLocalizationWeight theta x y := by
  simp only [thetaLocalizationWeight_eq_cos, ccmScaledPhaseAngle_apply]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp only [hx, hy, mul_zero, sub_zero, zero_sub, sub_self, Real.cos_zero,
      Real.cos_neg, Real.cos_pi, div_mul_cancel₀ t Real.pi_ne_zero] <;> ring

theorem ccmThetaLocalizationCross_scaledPhase {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (hphase : ∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) (t x y : ℝ) :
    ccmThetaLocalizationCross u (ccmScaledPhaseAngle theta t) x y =
      ((1 - Real.cos t) / 2) * ccmThetaLocalizationCross u theta x y := by
  by_cases hx : u x = 0
  · simp [ccmThetaLocalizationCross, hx]
  by_cases hy : u y = 0
  · simp [ccmThetaLocalizationCross, hy]
  rw [ccmThetaLocalizationCross, thetaLocalizationWeight_scaledPhase theta t x y
    (hphase x hx) (hphase y hy), ccmThetaLocalizationCross, mul_assoc]

theorem ccmThetaPrimeLocalizationError_scaledPhase {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (hphase : ∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) (t : ℝ) :
    ccmThetaPrimeLocalizationError u (ccmScaledPhaseAngle theta t) =
      ((1 - Real.cos t) / 2) * ccmThetaPrimeLocalizationError u theta := by
  unfold ccmThetaPrimeLocalizationError ccmThetaPrimeLocalizationDensity
  simp_rw [ccmThetaLocalizationCross_scaledPhase u theta hphase t]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  ring

theorem ccmThetaContinuousLocalizationError_scaledPhase {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (hphase : ∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) (t : ℝ) :
    ccmThetaContinuousLocalizationError u (ccmScaledPhaseAngle theta t) =
      ((1 - Real.cos t) / 2) * ccmThetaContinuousLocalizationError u theta := by
  unfold ccmThetaContinuousLocalizationError ccmThetaContinuousLocalizationDensity
  simp_rw [ccmThetaLocalizationCross_scaledPhase u theta hphase t]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  ring

/-- The phase dependence of the full actual quadratic is exactly sinusoidal. -/
theorem ccmPhaseLocalizationEnergy_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (hphase : ∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) (t : ℝ) :
    ccmPhaseLocalizationEnergy u theta t = ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
      ((ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2) *
        (1 - Real.cos t) := by
  have h := ccmRestrictedWeilSourceQuadratic_localization u (ccmScaledPhaseAngle theta t)
  rw [ccmThetaPrimeLocalizationError_scaledPhase u theta hphase,
    ccmThetaContinuousLocalizationError_scaledPhase u theta hphase] at h
  unfold ccmPhaseLocalizationEnergy
  linarith

theorem hasDerivAt_ccmPhaseLocalizationEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (hphase : ∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) (t : ℝ) :
    HasDerivAt (ccmPhaseLocalizationEnergy u theta)
      (((ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2) *
        Real.sin t) t := by
  have he : ccmPhaseLocalizationEnergy u theta = fun t =>
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
        ((ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2) *
          (1 - Real.cos t) := funext (ccmPhaseLocalizationEnergy_eq u theta hphase)
  rw [he]
  simpa only [neg_neg] using (((Real.hasDerivAt_cos t).const_sub 1).const_mul
    ((ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2)).const_add
      (ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector)

/-- An unconditional, nonconstant, prime-free phase potential in the actual arithmetic corpus. -/
theorem exists_ccmArithmetic_positive_phase_potential :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B : ℝ),
      0 < B ∧ HasCompactSupport theta ∧
      (∀ x ∈ Function.support u, theta x = 0 ∨ theta x = Real.pi) ∧
      (∀ t : ℝ, ccmThetaPrimeLocalizationError u (ccmScaledPhaseAngle theta t) = 0) ∧
      (∀ t : ℝ, ccmPhaseLocalizationEnergy u theta t =
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + B * (1 - Real.cos t)) ∧
      (∀ t : ℝ, HasDerivAt (ccmPhaseLocalizationEnergy u theta) (B * Real.sin t) t) := by
  obtain ⟨a, u, v, theta, htc, _, hphase, _, _, _, _, hp, _, hc, _, _⟩ :=
    exists_ccmTheta_localization_error_both_signs
  let B := (ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta) / 2
  have hB : 0 < B := by dsimp [B]; rw [hp]; linarith
  refine ⟨a, u, theta, B, hB, htc, hphase, ?_, ?_, ?_⟩
  · intro t
    rw [ccmThetaPrimeLocalizationError_scaledPhase u theta hphase, hp, mul_zero]
  · exact ccmPhaseLocalizationEnergy_eq u theta hphase
  · exact hasDerivAt_ccmPhaseLocalizationEnergy u theta hphase

end RHTower
