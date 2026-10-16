import GaloisForLFunctions.RHTower.PaperThetaNativeGrushinArithmetic
import GaloisForLFunctions.RHTower.PaperThetaNativeScalarReduction

/-! # One actual source channel repairs the native pencil globally

The original uniform space itself carries an entire family of automorphisms.
Its rank-one source repair and its inverse are explicit blocks of the
constructed native inverse, with no parameter exclusions.
-/

noncomputable section
open Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph

def nativeGrushinInputInverse (z : ℂ) : NativeContinuousSpace →L[ℂ] NativeGrushinSpace :=
  (nativeGrushinInverse z).comp (ContinuousLinearMap.inl ℂ NativeContinuousSpace ℂ)

def nativeGrushinSourceRow (z : ℂ) : NativeContinuousSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ).comp (nativeGrushinInputInverse z)

def nativeRepairedPencil (z : ℂ) : NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  nativePencil z+(nativeEffectiveScalar z-1) •
    (boundedResolventTrace nativeCompactParameter).smulRight (nativeCounterSource z)

def nativeRepairedInverse (z : ℂ) : NativeContinuousSpace →L[ℂ] NativeContinuousSpace :=
  (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).comp (nativeGrushinInputInverse z)-
    (nativeGrushinTraceResponse z).comp (nativeGrushinSourceRow z)

theorem nativeRepairedInverse_trace (z : ℂ) (g : NativeContinuousSpace) :
    boundedResolventTrace nativeCompactParameter (nativeRepairedInverse z g) =
      -nativeGrushinSourceRow z g := by
  change boundedResolventTrace nativeCompactParameter
    ((nativeGrushinInverse z (g,0)).1-nativeGrushinTraceResponse z (nativeGrushinSourceRow z g)) = _
  rw [map_sub]
  have hr : boundedResolventTrace nativeCompactParameter (nativeGrushinInverse z (g,0)).1 = 0 :=
    congrArg Prod.snd (nativeGrushinInverse_right z (g,0))
  have hu : boundedResolventTrace nativeCompactParameter
      (nativeGrushinTraceResponse z (nativeGrushinSourceRow z g)) = nativeGrushinSourceRow z g :=
    congrArg Prod.snd (nativeGrushinInverse_right z (0,nativeGrushinSourceRow z g))
  rw [hr,hu,zero_sub]

theorem nativeRepairedPencil_right (z : ℂ) (g : NativeContinuousSpace) :
    nativeRepairedPencil z (nativeRepairedInverse z g) = g := by
  ext x
  let c := nativeGrushinSourceRow z g
  have hr := congrArg (fun p : NativeGrushinSpace => p.1 x) (nativeGrushinInverse_right z (g,0))
  have hu := congrArg (fun p : NativeGrushinSpace => p.1 x) (nativeGrushinInverse_right z (0,c))
  change nativePencil z (nativeGrushinInverse z (g,0)).1 x+c*nativeCounterSource z x = g x at hr
  change nativePencil z (nativeGrushinTraceResponse z c) x+
    (nativeGrushinInverse z (0,c)).2*nativeCounterSource z x = 0 at hu
  rw [nativeGrushinInverse_scalar_zero] at hu
  change nativePencil z (nativeRepairedInverse z g) x+
    (nativeEffectiveScalar z-1)*(boundedResolventTrace nativeCompactParameter
      (nativeRepairedInverse z g)*nativeCounterSource z x) = g x
  rw [nativeRepairedInverse_trace]
  change nativePencil z ((nativeGrushinInverse z (g,0)).1-nativeGrushinTraceResponse z c) x+
    (nativeEffectiveScalar z-1)*((-c)*nativeCounterSource z x) = g x
  rw [map_sub]
  change nativePencil z (nativeGrushinInverse z (g,0)).1 x-
    nativePencil z (nativeGrushinTraceResponse z c) x+
      (nativeEffectiveScalar z-1)*((-c)*nativeCounterSource z x) = g x
  linear_combination hr-hu

private theorem nativeRepairedPencil_ker (z : ℂ) (v : NativeContinuousSpace)
    (hv : nativeRepairedPencil z v = 0) : v = 0 := by
  let t := boundedResolventTrace nativeCompactParameter v
  have hb : nativeGrushinBlock z (v,(nativeEffectiveScalar z-1)*t) = (0,t) := by
    apply Prod.ext
    · change nativePencil z v+((nativeEffectiveScalar z-1)*t) • nativeCounterSource z = 0
      have h : nativePencil z v+(nativeEffectiveScalar z-1) • (t • nativeCounterSource z) = 0 := hv
      simpa only [smul_smul] using h
    · rfl
  have hi := nativeGrushinInverse_left z (v,(nativeEffectiveScalar z-1)*t)
  rw [hb] at hi
  have hs := congrArg Prod.snd hi
  rw [nativeGrushinInverse_scalar_zero] at hs
  have ht : t = 0 := by linear_combination hs
  have hb0 : nativeGrushinBlock z (v,0) = 0 := by
    have h : nativeGrushinBlock z (v,0) = (0,0) := by simpa only [ht,mul_zero] using hb
    exact h.trans (Prod.ext rfl rfl)
  exact congrArg Prod.fst (nativeGrushinBlock_ker z (v,0) hb0)

theorem nativeRepairedPencil_injective (z : ℂ) : Function.Injective (nativeRepairedPencil z) := by
  intro v w h
  apply sub_eq_zero.mp
  apply nativeRepairedPencil_ker z
  rw [map_sub,h,sub_self]

theorem nativeRepairedPencil_left (z : ℂ) (v : NativeContinuousSpace) :
    nativeRepairedInverse z (nativeRepairedPencil z v) = v :=
  nativeRepairedPencil_injective z (nativeRepairedPencil_right z (nativeRepairedPencil z v))

theorem isUnit_nativeRepairedPencil (z : ℂ) : IsUnit (nativeRepairedPencil z) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨nativeRepairedPencil_injective z, fun g => ⟨nativeRepairedInverse z g,nativeRepairedPencil_right z g⟩⟩

theorem differentiable_nativeEffectiveScalar : Differentiable ℂ nativeEffectiveScalar := by
  have he : nativeEffectiveScalar = fun z =>
      (z/((HedenmalmThetaSource.thetaSource.mass : ℂ)*(nativeCounterMass : ℂ)))*XiC z :=
    funext nativeEffectiveScalar_eq
  rw [he]
  exact (differentiable_id.div_const _).mul XiC_differentiable

theorem differentiable_nativeRepairedPencil : Differentiable ℂ nativeRepairedPencil := by
  have hb := ((ContinuousLinearMap.smulRightL ℂ NativeContinuousSpace NativeContinuousSpace
    (boundedResolventTrace nativeCompactParameter)).differentiable).comp differentiable_nativeCounterSource
  exact differentiable_nativePencil.add
    ((differentiable_nativeEffectiveScalar.sub_const 1).smul hb)

theorem differentiable_nativeRepairedInverse : Differentiable ℂ nativeRepairedInverse := by
  have hp : Differentiable ℂ nativeGrushinInputInverse :=
    differentiable_nativeGrushinInverse.clm_comp
      (differentiable_const (ContinuousLinearMap.inl ℂ NativeContinuousSpace ℂ))
  have hc : Differentiable ℂ nativeGrushinSourceRow :=
    (differentiable_const (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)).clm_comp hp
  exact ((differentiable_const (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ)).clm_comp hp).sub
    (differentiable_nativeGrushinTraceResponse.clm_comp hc)

/-- An explicit entire automorphism and inverse on the original native space,
obtained by one literal compact source channel at every complex parameter. -/
theorem nativePencil_entire_source_repair :
    Differentiable ℂ nativeRepairedPencil ∧ Differentiable ℂ nativeRepairedInverse ∧
      ∀ z : ℂ, IsUnit (nativeRepairedPencil z) ∧
        (∀ g, nativeRepairedPencil z (nativeRepairedInverse z g) = g) ∧
        (∀ v, nativeRepairedInverse z (nativeRepairedPencil z v) = v) :=
  ⟨differentiable_nativeRepairedPencil,differentiable_nativeRepairedInverse,
    fun z => ⟨isUnit_nativeRepairedPencil z,nativeRepairedPencil_right z,nativeRepairedPencil_left z⟩⟩

/-- A literal native solution, with trace fixed by the actual theta moment. -/
def nativeRepairedNativeSolution (z : ℂ) (g : ThetaContinuousBV) : ThetaNativeDomain :=
  nativeGrushinBV z g (-nativeBoundaryCorrection z (nativeBVUniform g) 0)

theorem nativeRepairedNativeSolution_equation (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    thetaSpatialAction (nativeRepairedNativeSolution z g) x-z*nativeRepairedNativeSolution z g x+
      (nativeEffectiveScalar z-1)*thetaTailTrace (nativeRepairedNativeSolution z g)*
        nativeCounterSource z x = g x := by
  have h := nativeGrushinBV_equation z g (-nativeBoundaryCorrection z (nativeBVUniform g) 0) x
  have hc : nativeBoundaryCorrection z (nativeBVUniform g)
      (-nativeBoundaryCorrection z (nativeBVUniform g) 0) =
      (nativeEffectiveScalar z-1)*(-nativeBoundaryCorrection z (nativeBVUniform g) 0) := by
    simp only [nativeBoundaryCorrection,nativeEffectiveScalar,mul_zero,zero_mul,add_zero]
    ring
  unfold nativeRepairedNativeSolution
  rw [nativeGrushinBV_trace]
  rwa [hc] at h

theorem nativeRepairedNativeSolution_unique (z : ℂ) (g : ThetaContinuousBV)
    (f : ThetaNativeDomain)
    (he : ∀ x, thetaSpatialAction f x-z*f x+
      (nativeEffectiveScalar z-1)*thetaTailTrace f*nativeCounterSource z x = g x) :
    f = nativeRepairedNativeSolution z g := by
  let t := thetaTailTrace f
  have ho (x : ℝ) : deriv f x+sourceLogDerivative x*(f x-t)+I*z*f x =
      -I*(g x-(nativeEffectiveScalar z-1)*t*nativeCounterSource z x) := by
    have h := he x
    rw [thetaSpatialAction] at h
    change I*(deriv f x+sourceLogDerivative x*(f x-t))-z*f x+
      (nativeEffectiveScalar z-1)*t*nativeCounterSource z x = g x at h
    linear_combination (norm := ring_nf) -I*h
    simp only [Complex.I_sq]
    ring
  have hm := boundedThetaMoment_source_equation z (nativeBVUniform f.toThetaContinuousBV)
    (nativeBVUniform g-((nativeEffectiveScalar z-1)*t) • nativeCounterSource z)
    t f.differentiable ho
  rw [map_sub,map_smul,nativeCounterSource_moment] at hm
  have hd : nativeEffectiveScalar z*(nativeCounterMass : ℂ) = z*flatConnection z :=
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')
  have ht : thetaTailTrace f = -nativeBoundaryCorrection z (nativeBVUniform g) 0 := by
    change t = -((boundedThetaMomentCLM z (nativeBVUniform g)+z*0*flatConnection z)/
      (nativeCounterMass : ℂ))
    simp only [mul_zero,zero_mul,add_zero]
    rw [← neg_div]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne')).2
    linear_combination hm+t*hd
  exact (nativeGrushinBV_unique z g _ f ((nativeEffectiveScalar z-1)*t) ht he).1

/-- All continuous BV forcing has one actual repaired solution at EVERY complex
parameter, with compact AC transport and the complete signed Weil expression. -/
theorem nativeRepaired_full_arithmetic (z : ℂ) (g : ThetaContinuousBV) :
    ∃! f : ThetaNativeDomain,
      (∀ x, thetaSpatialAction f x-z*f x+
        (nativeEffectiveScalar z-1)*thetaTailTrace f*nativeCounterSource z x = g x) ∧
      AbsolutelyContinuousOnInterval (nativeClosedQuantile f) 0 1 ∧
      ∀ L : ℂ →L[ℝ] ℝ,
        sourceWeilEnergy (nativeWeilGraph f L) =
          ThetaQuantileArithmetic.weilEnergy (fun t => L (nativeClosedQuantile f t)) := by
  refine ⟨nativeRepairedNativeSolution z g,
    ⟨nativeRepairedNativeSolution_equation z g,
      absolutelyContinuousOnInterval_nativeClosedQuantile _,fun L => nativeWeilGraph_quantile _ L⟩, ?_⟩
  intro f hf
  exact nativeRepairedNativeSolution_unique z g f hf.1

end RHTower.PaperThetaEndpoint
