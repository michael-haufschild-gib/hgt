import GaloisForLFunctions.RHTower.PaperThetaNativeGrushin
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Entire native inversion and its exact scalar source entry

The augmented inverse is entire in operator norm, including all multiple Xi
zeros. Its scalar output is the literal theta character obstruction.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

theorem differentiable_nativePencil : Differentiable ℂ nativePencil :=
  (differentiable_const _).add
    (((differentiable_const I).sub differentiable_id).smul_const nativeCompactResolvent)

theorem differentiable_nativeGrushinBlock : Differentiable ℂ nativeGrushinBlock := by
  let F := ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ
  let S := ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ
  have h₁ := differentiable_nativePencil.clm_comp (differentiable_const F)
  have h₂ := ((ContinuousLinearMap.smulRightL ℂ NativeGrushinSpace NativeContinuousSpace S).differentiable).comp
    differentiable_nativeCounterSource
  have hp : Differentiable ℂ (fun p :
      (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) × (NativeGrushinSpace →L[ℂ] ℂ) =>
      p.1.prod p.2) := (ContinuousLinearMap.prodL ℂ :
    ((NativeGrushinSpace →L[ℂ] NativeContinuousSpace) × (NativeGrushinSpace →L[ℂ] ℂ)) ≃L[ℂ]
      (NativeGrushinSpace →L[ℂ] NativeGrushinSpace)).toContinuousLinearMap.differentiable
  exact Differentiable.comp (𝕜 := ℂ) (E := ℂ)
    (F := (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) × (NativeGrushinSpace →L[ℂ] ℂ))
    (G := NativeGrushinSpace →L[ℂ] NativeGrushinSpace) hp
    ((h₁.add h₂).prodMk (differentiable_const ((boundedResolventTrace nativeCompactParameter).comp F)))

def nativeGrushinInverse (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeGrushinSpace :=
  Ring.inverse (nativeGrushinBlock z)

theorem nativeGrushinInverse_left (z : ℂ) (p : NativeGrushinSpace) :
    nativeGrushinInverse z (nativeGrushinBlock z p) = p :=
  congrArg (fun T : NativeGrushinSpace →L[ℂ] NativeGrushinSpace => T p)
    (Ring.inverse_mul_cancel _ (isUnit_nativeGrushinBlock z))

theorem nativeGrushinInverse_right (z : ℂ) (p : NativeGrushinSpace) :
    nativeGrushinBlock z (nativeGrushinInverse z p) = p :=
  congrArg (fun T : NativeGrushinSpace →L[ℂ] NativeGrushinSpace => T p)
    (Ring.mul_inverse_cancel _ (isUnit_nativeGrushinBlock z))

/-- Operator-norm entire inversion on the whole original uniform space. -/
theorem differentiable_nativeGrushinInverse : Differentiable ℂ nativeGrushinInverse := by
  change Differentiable ℂ (fun z => Ring.inverse (nativeGrushinBlock z))
  intro z
  have hi : DifferentiableAt ℂ
      (Ring.inverse : (NativeGrushinSpace →L[ℂ] NativeGrushinSpace) →
        (NativeGrushinSpace →L[ℂ] NativeGrushinSpace)) (nativeGrushinBlock z) :=
    differentiableAt_inverse (𝕜 := ℂ) (R := NativeGrushinSpace →L[ℂ] NativeGrushinSpace)
      (isUnit_nativeGrushinBlock z)
  exact DifferentiableAt.comp (𝕜 := ℂ) (E := ℂ)
    (F := NativeGrushinSpace →L[ℂ] NativeGrushinSpace)
    (G := NativeGrushinSpace →L[ℂ] NativeGrushinSpace) z hi
    (differentiable_nativeGrushinBlock z)

theorem nativeGrushinInverse_scalar (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    (nativeGrushinInverse z (g,t)).2 = nativeBoundaryCorrection z g t := by
  let p := nativeGrushinInverse z (g,t)
  have he : nativePencil z p.1+p.2 • nativeCounterSource z = g :=
    congrArg Prod.fst (nativeGrushinInverse_right z (g,t))
  have ht : boundedResolventTrace nativeCompactParameter p.1 = t :=
    congrArg Prod.snd (nativeGrushinInverse_right z (g,t))
  have hm := nativeCompactResolvent_moment z p.1
  rw [ht] at hm
  have hc := congrArg (boundedThetaMomentCLM z) he
  rw [map_add, map_smul, nativeCounterSource_moment] at hc
  change p.2 = (boundedThetaMomentCLM z g+z*t*flatConnection z)/(nativeCounterMass : ℂ)
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')).2
  change boundedThetaMomentCLM z (p.1+(I-z) • nativeCompactResolvent p.1)+
    p.2*(nativeCounterMass : ℂ) = boundedThetaMomentCLM z g at hc
  linear_combination hc-hm

def nativeEffectiveScalar (z : ℂ) : ℂ := z*flatConnection z/(nativeCounterMass : ℂ)

theorem nativeGrushinInverse_scalar_zero (z t : ℂ) :
    (nativeGrushinInverse z (0,t)).2 = nativeEffectiveScalar z*t := by
  rw [nativeGrushinInverse_scalar]
  simp only [nativeBoundaryCorrection, map_zero, zero_add, nativeEffectiveScalar]
  ring

def nativeGrushinTraceResponse (z : ℂ) : ℂ →L[ℂ] NativeContinuousSpace :=
  (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).comp
    ((nativeGrushinInverse z).comp (ContinuousLinearMap.inr ℂ NativeContinuousSpace ℂ))

@[simp] theorem nativeGrushinTraceResponse_apply (z c : ℂ) :
    nativeGrushinTraceResponse z c = (nativeGrushinInverse z (0,c)).1 := rfl

theorem differentiable_nativeGrushinTraceResponse : Differentiable ℂ nativeGrushinTraceResponse :=
  (differentiable_const _).clm_comp
    (differentiable_nativeGrushinInverse.clm_comp (differentiable_const _))

/-- The inverse block gives actual spatial functions through the fixed Green operator. -/
def nativeGrushinProfile (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeContinuousSpace :=
  nativeCompactResolvent.comp ((ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).comp
    (nativeGrushinInverse z))

theorem differentiable_nativeGrushinProfile : Differentiable ℂ nativeGrushinProfile :=
  (differentiable_const _).clm_comp
    ((differentiable_const _).clm_comp differentiable_nativeGrushinInverse)

theorem nativeGrushinProfile_trace (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    thetaTailTrace (nativeGrushinProfile z (g,t)) = t := by
  have ht := congrArg Prod.snd (nativeGrushinInverse_right z (g,t))
  change boundedResolventTrace nativeCompactParameter (nativeGrushinInverse z (g,t)).1 = t at ht
  change thetaTailTrace (boundedNativeResolvent nativeCompactParameter
    (nativeGrushinInverse z (g,t)).1) = t
  rw [boundedNativeResolvent_trace]
  exact ht

theorem nativeGrushinProfile_equation (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) (x : ℝ) :
    thetaSpatialAction (nativeGrushinProfile z (g,t)) x-z*nativeGrushinProfile z (g,t) x+
      nativeBoundaryCorrection z g t*nativeCounterSource z x = g x := by
  let v := (nativeGrushinInverse z (g,t)).1
  have he := congrArg (fun p : NativeGrushinSpace => p.1 x) (nativeGrushinInverse_right z (g,t))
  change v x+(I-z)*nativeCompactResolvent v x+
    (nativeGrushinInverse z (g,t)).2*nativeCounterSource z x = g x at he
  rw [nativeGrushinInverse_scalar] at he
  have h := boundedNativeResolvent_equation nativeCompactParameter v x
  rw [nativeCompactParameter_val] at h
  change thetaSpatialAction (nativeCompactResolvent v) x-z*nativeCompactResolvent v x+
    nativeBoundaryCorrection z g t*nativeCounterSource z x = g x
  dsimp only [nativeCompactResolvent] at he ⊢
  linear_combination he+h

theorem nativeGrushinProfile_atTop (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    Tendsto (nativeGrushinProfile z (g,t)) atTop (𝓝 t) := by
  have h := boundedNativeResolvent_atTop nativeCompactParameter (nativeGrushinInverse z (g,t)).1
  have ht : boundedResolventTrace nativeCompactParameter (nativeGrushinInverse z (g,t)).1 = t :=
    congrArg Prod.snd (nativeGrushinInverse_right z (g,t))
  rw [ht] at h
  exact h

theorem nativeGrushinProfile_differentiable (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    Differentiable ℝ (nativeGrushinProfile z (g,t)) :=
  fun x => (hasDerivAt_boundedNativeResolvent nativeCompactParameter
    (nativeGrushinInverse z (g,t)).1 x).differentiableAt

/-- The Banach inverse is the literal two-ended Green construction. -/
theorem nativeGrushinProfile_eq_solution (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    nativeGrushinProfile z (g,t) = nativeGrushinSolution z g t := by
  let f := nativeGrushinProfile z (g,t)
  let h := nativeGrushinSolution z g t
  have hv : Differentiable ℝ (fun x => f x-h x) :=
    (nativeGrushinProfile_differentiable z g t).sub (nativeGrushinSolution_differentiable z g t)
  have ht : Tendsto (fun x => f x-h x) atTop (𝓝 0) := by
    simpa only [sub_self] using (nativeGrushinProfile_atTop z g t).sub (nativeGrushinSolution_atTop z g t)
  have hz := nativeODE_zero_of_trace_zero z (fun x => f x-h x) hv ht (fun x => ?_)
  · ext x
    exact sub_eq_zero.mp (congrFun hz x)
  · rw [show deriv (fun y => f y-h y) x = deriv f x-deriv h x from
      deriv_sub (nativeGrushinProfile_differentiable z g t x)
        (nativeGrushinSolution_differentiable z g t x)]
    have he := nativeGrushinProfile_equation z g t x
    rw [thetaSpatialAction, nativeGrushinProfile_trace] at he
    have hh := nativeGrushinSolution_ode z g t x
    change I*(deriv f x+sourceLogDerivative x*(f x-t))-z*f x+
      nativeBoundaryCorrection z g t*nativeCounterSource z x = g x at he
    change deriv h x+sourceLogDerivative x*(h x-t)+I*z*h x =
      -I*(g x-nativeBoundaryCorrection z g t*nativeCounterSource z x) at hh
    linear_combination (norm := ring_nf) -I*he-hh
    simp only [Complex.I_sq]
    ring

def nativeGrushinAction (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeContinuousSpace :=
  (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).comp (nativeGrushinInverse z)+
    I • nativeGrushinProfile z

theorem differentiable_nativeGrushinAction : Differentiable ℂ nativeGrushinAction := by
  change Differentiable ℂ (fun z =>
    (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).comp (nativeGrushinInverse z)+
      I • nativeGrushinProfile z)
  exact ((differentiable_const (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ)).clm_comp
    differentiable_nativeGrushinInverse).add
    ((differentiable_const I).smul differentiable_nativeGrushinProfile)

/-- The entire second coordinate is the literal spatial differential action. -/
theorem nativeGrushinAction_eq (z : ℂ) (p : NativeGrushinSpace) (x : ℝ) :
    nativeGrushinAction z p x = thetaSpatialAction (nativeGrushinProfile z p) x := by
  have h := boundedNativeResolvent_equation nativeCompactParameter (nativeGrushinInverse z p).1 x
  rw [nativeCompactParameter_val] at h
  change (nativeGrushinInverse z p).1 x+I*boundedNativeResolvent nativeCompactParameter
    (nativeGrushinInverse z p).1 x =
    thetaSpatialAction (boundedNativeResolvent nativeCompactParameter (nativeGrushinInverse z p).1) x
  linear_combination -h

/-- Entire continuation holds simultaneously for the function and its actual
spatial derivative expression, in the original uniform graph coordinates. -/
theorem differentiable_nativeGrushinGraph :
    Differentiable ℂ (fun z => (nativeGrushinProfile z).prod (nativeGrushinAction z)) := by
  have hp : Differentiable ℂ (fun p :
      (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) ×
        (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) => p.1.prod p.2) :=
    (ContinuousLinearMap.prodL ℂ :
    ((NativeGrushinSpace →L[ℂ] NativeContinuousSpace) ×
      (NativeGrushinSpace →L[ℂ] NativeContinuousSpace)) ≃L[ℂ]
      (NativeGrushinSpace →L[ℂ] NativeContinuousSpace × NativeContinuousSpace)).toContinuousLinearMap.differentiable
  exact Differentiable.comp (𝕜 := ℂ) (E := ℂ)
    (F := (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) ×
      (NativeGrushinSpace →L[ℂ] NativeContinuousSpace))
    (G := NativeGrushinSpace →L[ℂ] NativeContinuousSpace × NativeContinuousSpace) hp
    (differentiable_nativeGrushinProfile.prodMk differentiable_nativeGrushinAction)

end RHTower.PaperThetaEndpoint
