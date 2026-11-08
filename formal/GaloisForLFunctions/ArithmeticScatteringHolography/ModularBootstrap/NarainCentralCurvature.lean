import GaloisForLFunctions.RHTower.XiMagnetizationGHSConcavity
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

/-!
# Real and strictly negative central xi curvature

Schwarz reflection and real derivative transport identify the third logarithmic xi jet at one with the unconditional strict real concavity invariant.
-/

open Complex RHTower
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Strict concavity of the real xi logarithmic derivative gives the complex third logarithmic jet at one. -/
theorem narainCentralXiCurvature_neg :
    (deriv (deriv (logDeriv xi)) (1 : ℂ)).re < 0 := by
  have ha : AnalyticAt ℂ (logDeriv xi) (1 : ℂ) := by
    simpa only [logDeriv, Pi.div_apply] using
      ((xi_differentiable.deriv).analyticAt (1 : ℂ)).div
        (xi_differentiable.analyticAt (1 : ℂ)) (by rw [xi_one]; norm_num)
  have hd : HasDerivAt (deriv (logDeriv xi))
      (deriv (deriv (logDeriv xi)) 1) ((1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ)) := by
    rw [show (1 / 2 : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 by norm_num]
    exact ha.deriv.differentiableAt.hasDerivAt
  have hf := (hasDerivAt_id ((1 / 2 : ℝ) : ℂ)).const_add (1 / 2)
  have hc := hd.comp ((1 / 2 : ℝ) : ℂ) hf
  simp only [mul_one] at hc
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (1 / 2 : ℝ) hc.comp_ofReal
  have he : deriv xiRealLogDeriv =
      fun w : ℝ => (deriv (logDeriv xi) (1 / 2 + (w : ℂ))).re :=
    funext fun w => (hasDerivAt_xiRealLogDeriv w).deriv
  have hval : deriv (deriv xiRealLogDeriv) (1 / 2) =
      (deriv (deriv (logDeriv xi)) (1 : ℂ)).re := by
    rw [he]
    exact hr.deriv
  rw [← hval]
  exact deriv2_xiRealLogDeriv_neg (by norm_num) (by norm_num)

/-- Schwarz symmetry makes the third logarithmic xi jet at one real. -/
theorem narainCentralXiCurvature_real :
    ((deriv (deriv (logDeriv xi)) (1 : ℂ)).re : ℂ) =
      deriv (deriv (logDeriv xi)) (1 : ℂ) := by
  have hs : (starRingEnd ℂ) ∘ logDeriv xi ∘ (starRingEnd ℂ) = logDeriv xi := by
    funext z
    simp [Function.comp_apply, logDeriv_apply, xi_deriv_conj, xi_conj]
  have hd : (starRingEnd ℂ) ∘ deriv (logDeriv xi) ∘ (starRingEnd ℂ) =
      deriv (logDeriv xi) := by rw [← deriv_conj_conj, hs]
  have hdd : (starRingEnd ℂ) ∘ deriv (deriv (logDeriv xi)) ∘ (starRingEnd ℂ) =
      deriv (deriv (logDeriv xi)) := by rw [← deriv_conj_conj, hd]
  have hi := congrArg Complex.im (congrFun hdd 1)
  simp only [Function.comp_apply, map_one, Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith only [hi]

#print axioms narainCentralXiCurvature_neg
#print axioms narainCentralXiCurvature_real
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
