import GaloisForLFunctions.RHTower.PaperThetaNativeAnalyticInverse
import GaloisForLFunctions.RHTower.PaperThetaCutDivisor

/-! # Global analytic reduction of the actual native pencil

Explicit invertible shears reduce the whole stabilized spatial pencil to
one scalar source entry. Its divisor retains every original Xi multiplicity.
-/

noncomputable section
open Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource

def nativeTraceShear : NativeGrushinSpace →L[ℂ] NativeGrushinSpace :=
  (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).prod
    ((ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)+
      (boundedResolventTrace nativeCompactParameter).comp
        (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ))

def nativeSolutionShear (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeGrushinSpace :=
  ((ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ)-
    (nativeGrushinTraceResponse z).comp (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)).prod
    (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)

def nativeStabilizedPencil (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeGrushinSpace :=
  ((nativePencil z).comp (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ)).prod
    (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)

def nativeScalarDiagonal (z : ℂ) : NativeGrushinSpace →L[ℂ] NativeGrushinSpace :=
  (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ).prod
    (nativeEffectiveScalar z • ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)

theorem isUnit_nativeTraceShear : IsUnit nativeTraceShear := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · intro p q h
    change (p.1,p.2+boundedResolventTrace nativeCompactParameter p.1) =
      (q.1,q.2+boundedResolventTrace nativeCompactParameter q.1) at h
    have h₁ := congrArg Prod.fst h
    change p.1 = q.1 at h₁
    have h₂ : p.2+boundedResolventTrace nativeCompactParameter p.1 =
        q.2+boundedResolventTrace nativeCompactParameter q.1 := congrArg Prod.snd h
    exact Prod.ext h₁ (add_right_cancel (by simpa only [h₁] using h₂))
  · rintro ⟨v,c⟩
    refine ⟨(v,c-boundedResolventTrace nativeCompactParameter v), ?_⟩
    change (v,c-boundedResolventTrace nativeCompactParameter v+
      boundedResolventTrace nativeCompactParameter v) = (v,c)
    rw [sub_add_cancel]

theorem isUnit_nativeSolutionShear (z : ℂ) : IsUnit (nativeSolutionShear z) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  constructor
  · intro p q h
    change (p.1-nativeGrushinTraceResponse z p.2,p.2) =
      (q.1-nativeGrushinTraceResponse z q.2,q.2) at h
    have h₂ := congrArg Prod.snd h
    change p.2 = q.2 at h₂
    have h₁ : p.1-nativeGrushinTraceResponse z p.2 = q.1-nativeGrushinTraceResponse z q.2 :=
      congrArg Prod.fst h
    rw [h₂] at h₁
    have hpq : p.1 = q.1 := by
      simpa only [sub_add_cancel] using
        (congrArg (fun v => v+nativeGrushinTraceResponse z q.2) h₁)
    exact Prod.ext hpq h₂
  · rintro ⟨v,c⟩
    refine ⟨(v+nativeGrushinTraceResponse z c,c), ?_⟩
    change (v+nativeGrushinTraceResponse z c-nativeGrushinTraceResponse z c,c) = (v,c)
    rw [add_sub_cancel_right]

theorem differentiable_nativeSolutionShear : Differentiable ℂ nativeSolutionShear := by
  have h := (differentiable_const (ContinuousLinearMap.fst ℂ NativeContinuousSpace ℂ)).sub
    (differentiable_nativeGrushinTraceResponse.clm_comp
      (differentiable_const (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)))
  have hp : Differentiable ℂ (fun p :
      (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) × (NativeGrushinSpace →L[ℂ] ℂ) =>
      p.1.prod p.2) := (ContinuousLinearMap.prodL ℂ :
    ((NativeGrushinSpace →L[ℂ] NativeContinuousSpace) × (NativeGrushinSpace →L[ℂ] ℂ)) ≃L[ℂ]
      (NativeGrushinSpace →L[ℂ] NativeGrushinSpace)).toContinuousLinearMap.differentiable
  exact Differentiable.comp (𝕜 := ℂ) (E := ℂ)
    (F := (NativeGrushinSpace →L[ℂ] NativeContinuousSpace) × (NativeGrushinSpace →L[ℂ] ℂ))
    (G := NativeGrushinSpace →L[ℂ] NativeGrushinSpace) hp
    (h.prodMk (differentiable_const (ContinuousLinearMap.snd ℂ NativeContinuousSpace ℂ)))

/-- Exact global analytic equivalence, on all uniform forcing coordinates. -/
theorem nativePencil_global_scalar_reduction (z : ℂ) :
    nativeGrushinInverse z * nativeStabilizedPencil z * nativeTraceShear * nativeSolutionShear z =
      nativeScalarDiagonal z := by
  apply ContinuousLinearMap.ext
  intro p
  let v := p.1-nativeGrushinTraceResponse z p.2
  have he : nativeStabilizedPencil z (nativeTraceShear (nativeSolutionShear z p)) =
      nativeGrushinBlock z (v,0)+(0,p.2) := by
    simp only [nativeStabilizedPencil,nativeTraceShear,nativeSolutionShear,
      nativeGrushinBlock_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      _root_.add_apply,_root_.sub_apply,
      zero_smul,add_zero,Prod.mk_add_mk]
    exact congrArg (fun c => (nativePencil z v,c)) (add_comm _ _)
  change nativeGrushinInverse z
    (nativeStabilizedPencil z (nativeTraceShear (nativeSolutionShear z p))) = nativeScalarDiagonal z p
  rw [he, map_add, nativeGrushinInverse_left]
  apply Prod.ext
  · change (p.1-nativeGrushinTraceResponse z p.2)+(nativeGrushinInverse z (0,p.2)).1 = p.1
    rw [nativeGrushinTraceResponse_apply, sub_add_cancel]
  · change 0+(nativeGrushinInverse z (0,p.2)).2 = nativeEffectiveScalar z*p.2
    rw [zero_add, nativeGrushinInverse_scalar_zero]

theorem nativeEffectiveScalar_eq (z : ℂ) :
    nativeEffectiveScalar z =
      (z/((thetaSource.mass : ℂ)*(nativeCounterMass : ℂ)))*XiC z := by
  rw [nativeEffectiveScalar, flatConnection_eq_all]
  ring

theorem nativeEffectiveScalar_zero_iff (z : ℂ) :
    nativeEffectiveScalar z = 0 ↔ z = 0 ∨ XiC z = 0 := by
  rw [nativeEffectiveScalar_eq]
  simp only [mul_eq_zero, div_eq_zero_iff,
    mul_ne_zero (Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero)
      (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne'), or_false]

/-- The scalar analytic entry retains the full original Meyer/HF multiplicity. -/
theorem nativeEffectiveScalar_order (rho : XiDivisorSupport) :
    analyticOrderAt nativeEffectiveScalar (xiSpectralPointSupport rho) =
      (xiSupportMultiplicity rho : ℕ∞) := by
  let z := xiSpectralPointSupport rho
  have hz : z ≠ 0 := by
    intro hzero
    have h := XiC_xiSpectralPoint_eq_zero
      (⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : XiZeroCopy)
    change XiC z = 0 at h
    exact XiC_zero_ne (hzero ▸ h)
  let a : ℂ → ℂ := fun w => w/((thetaSource.mass : ℂ)*(nativeCounterMass : ℂ))
  have ha : AnalyticAt ℂ a z := (differentiable_id.div_const _).analyticAt z
  have ha0 : a z ≠ 0 := div_ne_zero hz
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero)
      (Complex.ofReal_ne_zero.mpr nativeCounterMass_pos.ne'))
  have he : nativeEffectiveScalar = a*XiC := funext nativeEffectiveScalar_eq
  rw [he, analyticOrderAt_mul ha (XiC_differentiable.analyticAt z),
    ha.analyticOrderAt_eq_zero.mpr ha0, zero_add, XiC_analyticOrderAt_support]
  rfl

end RHTower.PaperThetaEndpoint
