import GaloisForLFunctions.RHTower.PaperThetaNativeCounterSource

/-! # A global native block inverse through every complex resonance

One compact source channel and the actual two-ended trace resolve the full
theta pencil on all bounded continuous forcing. No Xi division is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

def nativeBoundaryCorrection (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) : ℂ :=
  (boundedThetaMomentCLM z g+z*t*flatConnection z)/(nativeCounterMass : ℂ)

def nativeCorrectedForcing (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) : NativeContinuousSpace :=
  g-nativeBoundaryCorrection z g t • nativeCounterSource z+(z*t) • nativeConstantCLM 1

theorem nativeCorrectedForcing_moment (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    boundedThetaMoment z (nativeCorrectedForcing z g t) = 0 := by
  change boundedThetaMomentCLM z (g-nativeBoundaryCorrection z g t • nativeCounterSource z+
    (z*t) • nativeConstantCLM 1) = 0
  rw [map_add, map_sub, map_smul, map_smul, nativeCounterSource_moment,
    boundedThetaMoment_constant, one_mul]
  dsimp [nativeBoundaryCorrection]
  rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')]
  ring

def nativeGrushinSolution (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) : NativeContinuousSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => t+I*boundedThetaTail z (nativeCorrectedForcing z g t) x)
    (continuous_const.add (continuous_const.mul (continuous_boundedThetaTail _ _)))
    (‖t‖+‖nativeCorrectedForcing z g t‖*(forcedTailMass z 0+forcedTailMass (-z) 0))
    (fun x => (norm_add_le _ _).trans (by
      simpa only [norm_mul, norm_I, one_mul] using
        add_le_add (le_refl ‖t‖) (norm_boundedThetaTail_global (nativeCorrectedForcing_moment z g t) x)))

@[simp] theorem nativeGrushinSolution_apply (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) (x : ℝ) :
    nativeGrushinSolution z g t x = t+I*boundedThetaTail z (nativeCorrectedForcing z g t) x := rfl

theorem nativeGrushinSolution_differentiable (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    Differentiable ℝ (nativeGrushinSolution z g t) := fun x =>
  (((hasDerivAt_boundedThetaTail z (nativeCorrectedForcing z g t) x).const_mul I).const_add t).differentiableAt

theorem nativeGrushinSolution_atTop (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    Tendsto (nativeGrushinSolution z g t) atTop (𝓝 t) := by
  change Tendsto (fun x => t+I*boundedThetaTail z (nativeCorrectedForcing z g t) x) atTop (𝓝 t)
  simpa only [mul_zero, add_zero] using
    ((tendsto_boundedThetaTail_atTop z (nativeCorrectedForcing z g t)).const_mul I).const_add t

theorem nativeGrushinSolution_atBot (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    Tendsto (nativeGrushinSolution z g t) atBot (𝓝 t) := by
  change Tendsto (fun x => t+I*boundedThetaTail z (nativeCorrectedForcing z g t) x) atBot (𝓝 t)
  simpa only [mul_zero, add_zero] using
    ((tendsto_boundedThetaTail_atBot (nativeCorrectedForcing_moment z g t)).const_mul I).const_add t

theorem nativeGrushinSolution_trace (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) :
    thetaTailTrace (nativeGrushinSolution z g t) = t := (nativeGrushinSolution_atTop z g t).limUnder_eq

theorem nativeGrushinSolution_ode (z : ℂ) (g : NativeContinuousSpace) (t : ℂ) (x : ℝ) :
    deriv (nativeGrushinSolution z g t) x+
      sourceLogDerivative x*(nativeGrushinSolution z g t x-t)+I*z*nativeGrushinSolution z g t x =
        -I*(g x-nativeBoundaryCorrection z g t*nativeCounterSource z x) := by
  have hd := (((hasDerivAt_boundedThetaTail z (nativeCorrectedForcing z g t) x).const_mul I).const_add t).deriv
  change deriv (nativeGrushinSolution z g t) x = _ at hd
  rw [hd, nativeGrushinSolution_apply]
  change I*(-(sourceLogDerivative x+I*z)*boundedThetaTail z (nativeCorrectedForcing z g t) x-
      (g x-nativeBoundaryCorrection z g t*nativeCounterSource z x+z*t*1))+
    sourceLogDerivative x*((t+I*boundedThetaTail z (nativeCorrectedForcing z g t) x)-t)+
    I*z*(t+I*boundedThetaTail z (nativeCorrectedForcing z g t) x) = _
  ring

def nativePencil (z : ℂ) : NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  1+(I-z) • nativeCompactResolvent

@[simp] theorem nativePencil_apply (z : ℂ) (v : NativeContinuousSpace) :
    nativePencil z v = v+(I-z) • nativeCompactResolvent v := rfl

abbrev NativeGrushinSpace := NativeContinuousSpace × ℂ

def nativeGrushinBlock (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeGrushinSpace :=
  (((nativePencil z).comp (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ))+
    (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ).smulRight (nativeCounterSource z)).prod
    ((boundedResolventTrace nativeCompactParameter).comp
      (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ))

@[simp] theorem nativeGrushinBlock_apply (z : ℂ) (p : NativeGrushinSpace) :
    nativeGrushinBlock z p =
      (nativePencil z p.1+p.2 • nativeCounterSource z, boundedResolventTrace nativeCompactParameter p.1) := rfl

theorem nativeGrushinBlock_surjective (z : ℂ) : Function.Surjective (nativeGrushinBlock z) := by
  rintro ⟨g, t⟩
  let f := nativeGrushinSolution z g t
  let c := nativeBoundaryCorrection z g t
  let v : NativeContinuousSpace := g-c • nativeCounterSource z+(z-I) • f
  have hK : f = nativeCompactResolvent v := by
    apply boundedNativeResolvent_unique nativeCompactParameter v f t
      (nativeGrushinSolution_differentiable z g t) (nativeGrushinSolution_atTop z g t)
    intro x
    rw [nativeCompactParameter_val]
    have h := nativeGrushinSolution_ode z g t x
    change deriv f x+sourceLogDerivative x*(f x-t)+I*I*f x =
      -I*(g x-c*nativeCounterSource z x+(z-I)*f x)
    change deriv f x+sourceLogDerivative x*(f x-t)+I*z*f x =
      -I*(g x-c*nativeCounterSource z x) at h
    linear_combination h
  refine ⟨(v,c), ?_⟩
  apply Prod.ext
  · change v+(I-z) • nativeCompactResolvent v+c • nativeCounterSource z = g
    rw [← hK]
    ext x
    change g x-c*nativeCounterSource z x+(z-I)*f x+(I-z)*f x+c*nativeCounterSource z x = g x
    ring
  · have ht := nativeGrushinSolution_trace z g t
    change thetaTailTrace f = t at ht
    rw [hK] at ht
    change thetaTailTrace (boundedNativeResolvent nativeCompactParameter v) = t at ht
    rw [boundedNativeResolvent_trace] at ht
    exact ht

theorem nativeGrushinBlock_ker (z : ℂ) (p : NativeGrushinSpace)
    (hp : nativeGrushinBlock z p = 0) : p = 0 := by
  rcases p with ⟨v,c⟩
  have he : nativePencil z v+c • nativeCounterSource z = 0 := congrArg Prod.fst hp
  have ht : boundedResolventTrace nativeCompactParameter v = 0 := congrArg Prod.snd hp
  have hm := nativeCompactResolvent_moment z v
  rw [ht, mul_zero, zero_mul, add_zero] at hm
  have hc := congrArg (boundedThetaMomentCLM z) he
  rw [map_add, map_smul, nativeCounterSource_moment, map_zero] at hc
  change boundedThetaMomentCLM z (v+(I-z) • nativeCompactResolvent v)+c*(nativeCounterMass : ℂ) = 0 at hc
  rw [hm, zero_add] at hc
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_right
    (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')
  rw [hc0, zero_smul, add_zero, nativePencil_apply] at he
  have hf := nativeODE_zero_of_trace_zero z (nativeCompactResolvent v)
    (fun x => (hasDerivAt_boundedNativeResolvent nativeCompactParameter v x).differentiableAt)
    (by simpa only [nativeCompactResolvent, ht] using
      boundedNativeResolvent_atTop nativeCompactParameter v) (fun x => ?_)
  · have hv : v = 0 := by
      ext x
      have hx := congrArg (fun u : NativeContinuousSpace => u x) he
      have hf0 := congrFun hf x
      change nativeCompactResolvent v x = 0 at hf0
      change v x+(I-z)*nativeCompactResolvent v x = 0 at hx
      change v x = 0
      simpa only [hf0, mul_zero, add_zero] using hx
    exact Prod.ext hv hc0
  · have h := boundedNativeResolvent_ode nativeCompactParameter v x
    rw [nativeCompactParameter_val, ht, sub_zero] at h
    have hx := congrArg (fun u : NativeContinuousSpace => u x) he
    change v x+(I-z)*nativeCompactResolvent v x = 0 at hx
    dsimp only [nativeCompactResolvent] at hx ⊢
    linear_combination h-I*hx

/-- The whole block pencil is invertible at every complex parameter. -/
theorem nativeGrushinBlock_bijective (z : ℂ) : Function.Bijective (nativeGrushinBlock z) := by
  refine ⟨?_, nativeGrushinBlock_surjective z⟩
  intro p q hpq
  apply sub_eq_zero.mp
  apply nativeGrushinBlock_ker z
  rw [map_sub, hpq, sub_self]

theorem isUnit_nativeGrushinBlock (z : ℂ) : IsUnit (nativeGrushinBlock z) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (nativeGrushinBlock_bijective z)

end RHTower.PaperThetaEndpoint
