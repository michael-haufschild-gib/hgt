import GaloisForLFunctions.RHTower.ThetaGammaPolarGroundDifference
import GaloisForLFunctions.RHTower.SuzukiCCMMixedSmoothCore

/-!
# Theta ground profiles cover the complete smooth CCM core

The actual theta source is smooth and strictly positive. Dividing a compact
smooth CCM source by it therefore gives a Schwartz profile, with no omitted
core tests. Both the prime and continuous jump energies of this profile are
absolutely convergent. This supplies the domain bridge required to compare
the theta relative form with the existing restricted Weil form.

This module establishes domain coverage, not equality or positivity of the
two quadratic forms.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

private theorem theta_ground_denominator_ne_zero (x : ℝ) :
    (thetaCuspFullSource x : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x).ne'

def ccmThetaGroundProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : 𝓢(ℝ, ℂ) :=
  suzukiComplexTestSchwartz (fun x => u x / (thetaCuspFullSource x : ℂ))
    (by
      convert! u.smooth.mul
        ((Complex.ofRealCLM.contDiff.comp contDiff_thetaCuspFullSource).inv
          theta_ground_denominator_ne_zero) using 1)
    (by
      have hs : HasCompactSupport (fun x => u x * (thetaCuspFullSource x : ℂ)⁻¹) :=
        u.hasCompactSupport.mul_right
      simpa only [div_eq_mul_inv] using hs)

theorem ccmThetaGroundProfile_apply {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    ccmThetaGroundProfile u x = u x / (thetaCuspFullSource x : ℂ) := rfl

/-- Every literal smooth CCM source is an actual theta source times a Schwartz profile. -/
theorem ccmThetaGroundProfile_reconstruct {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    (thetaCuspFullSource x : ℂ) * ccmThetaGroundProfile u x = u x := by
  rw [ccmThetaGroundProfile_apply]
  have hk := theta_ground_denominator_ne_zero x
  field_simp

/-- Domain coverage includes convergence of both arithmetic energies. -/
theorem ccmSmoothCore_exists_convergent_thetaGroundProfile
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    ∃ chi : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, (thetaCuspFullSource x : ℂ) * chi x = u x) ∧
      Integrable (thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
        chi.toBoundedContinuousFunction) thetaPrimeLinkMeasure ∧
      Integrable (thetaGammaPolarScalingDensity thetaCuspTiltSource chi) thetaContinuousLinkMeasure :=
  ⟨ccmThetaGroundProfile u, ccmThetaGroundProfile_reconstruct u,
    integrable_thetaPrimeScalingEnergyDensity _ _ _,
    integrable_thetaGammaPolarScalingDensity _ _⟩

end RHTower
