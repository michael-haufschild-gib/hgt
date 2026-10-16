import GaloisForLFunctions.RHTower.PaperThetaCompactNativeResolvent
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The exact character obstruction for whole native forcing

Integrating the weighted native differential equation retains its actual
trace. The resulting moment identity applies on the entire uniform domain.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource

theorem boundedThetaMoment_source_equation (z : ℂ) (f g : NativeContinuousSpace) (t : ℂ)
    (hf : Differentiable ℝ f)
    (he : ∀ x, deriv f x+sourceLogDerivative x*(f x-t)+I*z*f x = -I*g x) :
    boundedThetaMomentCLM z g+z*t*flatConnection z = 0 := by
  let v : NativeContinuousSpace := f-nativeConstantCLM t
  let h : NativeContinuousSpace := g+(z*t) • nativeConstantCLM 1
  let w : ℝ → ℂ := fun x => flatCharDensity z x*v x
  have hd (x : ℝ) : HasDerivAt w (-I*(flatCharDensity z x*h x)) x := by
    have hρ := ((differentiable_normalized_theta x).hasDerivAt.ofReal_comp).differentiableAt.hasDerivAt
    have hc : HasDerivAt (sourceChar z) (I*z*sourceChar z x) x := by
      change HasDerivAt (fun y : ℝ => exp (I*z*(y : ℂ)))
        (I*z*exp (I*z*(x : ℂ))) x
      simpa [mul_comm] using (((hasDerivAt_id (x : ℂ)).const_mul (I*z)).cexp).comp_ofReal
    have hρ0 : (thetaSource.normalized x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
    have hx := he x
    dsimp [sourceLogDerivative] at hx
    field_simp at hx
    refine ((hρ.mul hc).mul ((hf x).hasDerivAt.sub_const t)).congr_deriv ?_
    change _ = -I*((thetaSource.normalized x : ℂ)*sourceChar z x*(g x+z*t*1))
    simp only [Pi.mul_apply]
    linear_combination sourceChar z x*hx
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd
    ((integrable_boundedThetaDensity z h).const_mul (-I))
    (integrable_boundedThetaDensity z v)
  rw [integral_const_mul] at hz
  have hm : boundedThetaMomentCLM z h = 0 :=
    (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr I_ne_zero)
  change boundedThetaMomentCLM z (g+(z*t) • nativeConstantCLM 1) = 0 at hm
  rw [map_add, map_smul, boundedThetaMoment_constant, one_mul] at hm
  exact hm

/-- The original compact inverse retains the full parameter-dependent character. -/
theorem nativeCompactResolvent_moment (z : ℂ) (v : NativeContinuousSpace) :
    boundedThetaMomentCLM z (v+(I-z) • nativeCompactResolvent v)+
      z*boundedResolventTrace nativeCompactParameter v*flatConnection z = 0 := by
  apply boundedThetaMoment_source_equation z _ _ _
    (fun x => (hasDerivAt_boundedNativeResolvent nativeCompactParameter v x).differentiableAt)
  intro x
  have h := boundedNativeResolvent_ode nativeCompactParameter v x
  rw [nativeCompactParameter_val] at h
  change deriv (nativeCompactResolvent v) x+
    sourceLogDerivative x*(nativeCompactResolvent v x-boundedResolventTrace nativeCompactParameter v)+
    I*z*nativeCompactResolvent v x = -I*(v x+(I-z)*nativeCompactResolvent v x)
  linear_combination h

end RHTower.PaperThetaEndpoint
