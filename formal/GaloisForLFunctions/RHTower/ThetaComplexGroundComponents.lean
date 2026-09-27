import GaloisForLFunctions.RHTower.ThetaRealTranslatedCoercivity

/-!
# Real and imaginary components of the complete theta ground form

The Gamma, prime, and polar terms all use real Hermitian correlations. Their
full energy and physical mass split exactly into real and imaginary component
energies. This supplies the complex-source extension of real coercivity bounds.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def thetaRealComponent (chi : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℝ) := chi.postcompCLM Complex.reCLM
def thetaImagComponent (chi : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℝ) := chi.postcompCLM Complex.imCLM

@[simp] theorem thetaRealComponent_apply (chi : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaRealComponent chi x = (chi x).re := rfl
@[simp] theorem thetaImagComponent_apply (chi : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaImagComponent chi x = (chi x).im := rfl

@[simp] theorem thetaRealComponent_add (chi eta : 𝓢(ℝ, ℂ)) :
    thetaRealComponent (chi + eta) = thetaRealComponent chi + thetaRealComponent eta :=
  map_add (SchwartzMap.postcompCLM Complex.reCLM) chi eta
@[simp] theorem thetaImagComponent_add (chi eta : 𝓢(ℝ, ℂ)) :
    thetaImagComponent (chi + eta) = thetaImagComponent chi + thetaImagComponent eta :=
  map_add (SchwartzMap.postcompCLM Complex.imCLM) chi eta
@[simp] theorem thetaRealComponent_sub (chi eta : 𝓢(ℝ, ℂ)) :
    thetaRealComponent (chi - eta) = thetaRealComponent chi - thetaRealComponent eta :=
  map_sub (SchwartzMap.postcompCLM Complex.reCLM) chi eta
@[simp] theorem thetaImagComponent_sub (chi eta : 𝓢(ℝ, ℂ)) :
    thetaImagComponent (chi - eta) = thetaImagComponent chi - thetaImagComponent eta :=
  map_sub (SchwartzMap.postcompCLM Complex.imCLM) chi eta

theorem support_thetaRealComponent_subset (chi : 𝓢(ℝ, ℂ)) :
    Function.support (thetaRealComponent chi) ⊆ Function.support chi := by
  intro x hx hz
  exact hx (by simp only [thetaRealComponent_apply, hz, Complex.zero_re])
theorem support_thetaImagComponent_subset (chi : 𝓢(ℝ, ℂ)) :
    Function.support (thetaImagComponent chi) ⊆ Function.support chi := by
  intro x hx hz
  exact hx (by simp only [thetaImagComponent_apply, hz, Complex.zero_im])

theorem hasCompactSupport_thetaRealComponent (chi : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport chi) :
    HasCompactSupport (thetaRealComponent chi) := hc.mono (support_thetaRealComponent_subset chi)
theorem hasCompactSupport_thetaImagComponent (chi : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport chi) :
    HasCompactSupport (thetaImagComponent chi) := hc.mono (support_thetaImagComponent_subset chi)

theorem thetaGroundNormDensity_realImag (chi : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaGroundNormDensity chi x =
      thetaGroundNormDensity (thetaComplexify (thetaRealComponent chi)) x +
      thetaGroundNormDensity (thetaComplexify (thetaImagComponent chi)) x := by
  simp only [thetaGroundNormDensity, thetaComplexify_apply, thetaRealComponent_apply,
    thetaImagComponent_apply, Complex.sq_norm, Complex.normSq_apply,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem thetaGroundNormSq_realImag (chi : 𝓢(ℝ, ℂ)) :
    thetaGroundNormSq chi = thetaGroundNormSq (thetaComplexify (thetaRealComponent chi)) +
      thetaGroundNormSq (thetaComplexify (thetaImagComponent chi)) := by
  unfold thetaGroundNormSq
  simp_rw [thetaGroundNormDensity_realImag chi]
  exact integral_add (integrable_thetaGroundNormDensity _) (integrable_thetaGroundNormDensity _)

theorem thetaGammaPolarQuadraticDensity_realImag (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) :
    thetaGammaPolarQuadraticDensity thetaCuspTiltSource chi p =
      thetaGammaPolarQuadraticDensity thetaCuspTiltSource
        (thetaComplexify (thetaRealComponent chi)) p +
      thetaGammaPolarQuadraticDensity thetaCuspTiltSource
        (thetaComplexify (thetaImagComponent chi)) p := by
  simp only [thetaGammaPolarQuadraticDensity, thetaComplexify_apply, thetaRealComponent_apply,
    thetaImagComponent_apply, Complex.sq_norm, Complex.normSq_apply,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem thetaPrimeScalingCrossDensity_realImag (chi : 𝓢(ℝ, ℂ)) (p : ℕ × ℝ) :
    thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        chi.toBoundedContinuousFunction p =
      thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (thetaRealComponent chi)).toBoundedContinuousFunction p +
      thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (thetaImagComponent chi)).toBoundedContinuousFunction p := by
  simp only [thetaPrimeScalingCrossDensity, SchwartzMap.toBoundedContinuousFunction_apply,
    thetaComplexify_apply, thetaRealComponent_apply, thetaImagComponent_apply,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem thetaPrimeScalingCross_realImag (chi : 𝓢(ℝ, ℂ)) :
    thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi.toBoundedContinuousFunction =
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (thetaRealComponent chi)).toBoundedContinuousFunction +
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (thetaImagComponent chi)).toBoundedContinuousFunction := by
  unfold thetaPrimeScalingCross
  simp_rw [thetaPrimeScalingCrossDensity_realImag chi]
  exact integral_add (integrable_thetaPrimeScalingCrossDensity _ _ _)
    (integrable_thetaPrimeScalingCrossDensity _ _ _)

/-- The exact full energy splits; no prime, Gamma, or pole term is dropped. -/
theorem thetaFullArithmeticQuadratic_realImag (chi : 𝓢(ℝ, ℂ)) :
    thetaFullArithmeticQuadratic chi =
      thetaRealArithmeticQuadratic (thetaRealComponent chi) +
      thetaRealArithmeticQuadratic (thetaImagComponent chi) := by
  have hg : (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource chi p
      ∂thetaContinuousLinkMeasure) =
      (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource
        (thetaComplexify (thetaRealComponent chi)) p ∂thetaContinuousLinkMeasure) +
      (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource
        (thetaComplexify (thetaImagComponent chi)) p ∂thetaContinuousLinkMeasure) := by
    simp_rw [thetaGammaPolarQuadraticDensity_realImag chi]
    exact integral_add (integrable_thetaGammaPolarQuadraticDensity _)
      (integrable_thetaGammaPolarQuadraticDensity _)
  unfold thetaRealArithmeticQuadratic thetaFullArithmeticQuadratic
  rw [hg, thetaGroundNormSq_realImag chi, thetaPrimeScalingCross_realImag chi]
  ring

end RHTower.ThetaSourceWard
