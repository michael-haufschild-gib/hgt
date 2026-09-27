import GaloisForLFunctions.RHTower.ThetaGammaPolarScalingEnergy
import GaloisForLFunctions.RHTower.ThetaPrimeGammaScalingEnergy

/-!
# The relative ground-state form of the continuous source

The diagonal and cross terms below retain the literal Gamma/pole translation
coefficients. Their difference is exactly the negative signed jump energy.
Absolute convergence is proved for this compensated difference before taking
its integral. No subtraction of divergent integrals is used.

Combining this correction with the proved prime diagonal identity gives the
relative form `prime energy - continuous energy`. Identifying this relative
form with a complete RH-equivalent spectral form remains a separate task.
-/

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def thetaGammaPolarDiagonalDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) : ℝ :=
  let a := Real.exp (-2 * p.1) / (1 - Real.exp (-2 * p.1))
  let b := thetaGammaPolarScalingKernel p.1
  S.k p.2 * (a * S.k p.2 + b * S.k (p.2 + p.1)) * ‖chi p.2‖ ^ 2 +
    S.k (p.2 + p.1) * (a * S.k (p.2 + p.1) + b * S.k p.2) * ‖chi (p.2 + p.1)‖ ^ 2

def thetaGammaPolarQuadraticDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-2 * p.1) / (1 - Real.exp (-2 * p.1)) *
      ((S.k p.2) ^ 2 * ‖chi p.2‖ ^ 2 + (S.k (p.2 + p.1)) ^ 2 * ‖chi (p.2 + p.1)‖ ^ 2) +
    2 * thetaGammaPolarScalingKernel p.1 * S.k p.2 * S.k (p.2 + p.1) *
      (chi (p.2 + p.1) * (starRingEnd ℂ) (chi p.2)).re

/-- These diagonal coefficients are the literal forward and reflected source actions. -/
theorem thetaGammaPolarDiagonalDensity_actual (chi : 𝓢(ℝ, ℂ)) (u x : ℝ) :
    thetaGammaPolarDiagonalDensity thetaCuspTiltSource chi (u, x) =
      thetaCuspFullSource x *
        ((gammaSourceTerm x u : ℂ) + polarSourceTerm (1 / 2) x u +
          polarSourceTerm (-1 / 2) x u).re * ‖chi x‖ ^ 2 +
      thetaCuspFullSource (x + u) *
        ((gammaSourceTerm (-x - u) u : ℂ) + polarSourceTerm (1 / 2) (-x - u) u +
          polarSourceTerm (-1 / 2) (-x - u) u).re * ‖chi (x + u)‖ ^ 2 := by
  rw [thetaGammaPolarScalingKernel_source_decomposition,
    thetaGammaPolarScalingKernel_source_decomposition]
  simp only [Complex.ofReal_re, show -x - u = -(x + u) by ring,
    show -(x + u) + u = -x by ring, thetaCuspFullSource_neg,
    thetaGammaPolarDiagonalDensity, thetaCuspTiltSource_k]

/-- The full continuous cross term survives the ground-state subtraction. -/
theorem thetaGammaPolar_ground_difference (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) :
    thetaGammaPolarQuadraticDensity S chi p - thetaGammaPolarDiagonalDensity S chi p =
      -thetaGammaPolarScalingDensity S chi p := by
  simp only [thetaGammaPolarQuadraticDensity, thetaGammaPolarDiagonalDensity,
    thetaGammaPolarScalingDensity, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  ring

theorem integrable_thetaGammaPolar_ground_difference (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    Integrable (fun p => thetaGammaPolarQuadraticDensity S chi p -
      thetaGammaPolarDiagonalDensity S chi p) thetaContinuousLinkMeasure := by
  convert! (integrable_thetaGammaPolarScalingDensity S chi).neg using 1
  ext p
  exact thetaGammaPolar_ground_difference S chi p

theorem integral_thetaGammaPolar_ground_difference (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    (∫ p, thetaGammaPolarQuadraticDensity S chi p - thetaGammaPolarDiagonalDensity S chi p
      ∂thetaContinuousLinkMeasure) = -thetaGammaPolarScalingEnergy S chi := by
  simp only [thetaGammaPolar_ground_difference, integral_neg, thetaGammaPolarScalingEnergy]

def thetaPrimeGammaPolarRelativeForm (chi : 𝓢(ℝ, ℂ)) : ℝ :=
  thetaPrimeGammaScalingDiagonal chi.toBoundedContinuousFunction -
    2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi.toBoundedContinuousFunction +
      ∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource chi p -
        thetaGammaPolarDiagonalDensity thetaCuspTiltSource chi p ∂thetaContinuousLinkMeasure

/-- An exact arithmetic reduction, with both the discrete and continuous energies retained. -/
theorem thetaPrimeGammaPolarRelativeForm_eq (chi : 𝓢(ℝ, ℂ)) :
    thetaPrimeGammaPolarRelativeForm chi =
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource chi.toBoundedContinuousFunction -
        thetaGammaPolarScalingEnergy thetaCuspTiltSource chi := by
  rw [thetaPrimeGammaPolarRelativeForm, thetaPrimeGammaScaling_identity,
    integral_thetaGammaPolar_ground_difference, sub_eq_add_neg]

end RHTower.ThetaSourceWard
