import GaloisForLFunctions.RHTower.SelbergScatteringForcingTransport
import GaloisForLFunctions.HTGeometry.CfcZeroSetKernel

/-!
# Exact native eigenspaces of the entire Xi forcing transport

The reciprocal symbol has one nonnegative preimage at each nonzero ordinate.
Continuous zero-set kernel comparison recovers precisely its original native
covariance eigenspace. Reality together with the lower range bound forces
critical placement for any nonzero full-Xi entire eigenvector. The actual native
resolvent commutes with the covariance, giving the exact kernel classification
for every original forcing vector. No eigenspace occurrence is asserted.
-/

open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace
namespace RHTower.SelbergScatteringEntireEigenvectors
open D4BMModularCore SelbergScatteringEntireOperator SelbergScatteringEntireTransform
open SelbergScatteringEntireXiPackets
noncomputable section

/-- The unique possible native energy of a full transformed Xi occurrence. -/
def xiNativeEigenvalue (q : XiZeroCopy) : ℝ := 1+nativePartner (q.1:ℂ).im

theorem xiNativeEigenvalue_pos (q : XiZeroCopy) : 0 < xiNativeEigenvalue q := by
  unfold xiNativeEigenvalue nativePartner
  positivity

/-- The reciprocal entire symbol has exactly one nonnegative preimage at every
nonzero real ordinate, including the covariance accumulation point zero. -/
theorem entireCovarianceSymbol_fibre (t : ℝ) (ht : t ≠ 0) (x : ℝ) (hx : 0 ≤ x) :
    entireCovarianceSymbol x = entireCovarianceSymbol ((1+nativePartner t)⁻¹) ↔
      x=(1+nativePartner t)⁻¹ := by
  have ha : 0 < 1+nativePartner t := by unfold nativePartner; positivity
  have hb : 0 < (1+nativePartner t)⁻¹ := inv_pos.mpr ha
  have harg : ((1+nativePartner t)⁻¹)⁻¹-1=nativePartner t := by simp
  constructor
  · intro he
    have hxpos : 0 < x := by
      by_contra hn
      have hx0 : x=0 := le_antisymm (le_of_not_gt hn) hx
      have h0 : entireCovarianceSymbol x=0 := (entireCovarianceSymbol_zero_iff x).mpr (by rw [hx0])
      have hp := entireCovarianceSymbol_pos hb
      rw [he] at h0
      linarith
    simp only [entireCovarianceSymbol,if_pos hxpos,if_pos hb,harg] at he
    have hr : (casimirTransform (x⁻¹-1:ℝ)).re = (casimirTransform (nativePartner t)).re := by
      have hi := inv_inj.mp he
      linarith
    have hc : casimirTransform (x⁻¹-1:ℝ)=casimirTransform (nativePartner t) :=
      Complex.ext hr (by rw [(casimirTransform_real_range _).1,(casimirTransform_real_range _).1])
    rw [casimirTransform_nativePartner] at hc
    have h := ((real_native_preimage_iff (t:ℂ) (by simpa using ht)
      (by norm_num) (by norm_num) (x⁻¹-1)).mp hc).2
    have hi : x⁻¹=1+nativePartner t := by
      simp only [Complex.ofReal_re] at h
      linarith
    calc x=(x⁻¹)⁻¹ := by simp
         _=(1+nativePartner t)⁻¹ := congrArg Inv.inv hi
  · intro he
    rw [he]

/-- Exact recovery of the original covariance eigenspace from the entire
reciprocal symbol. This proves equivalence, not occurrence of an eigenvector. -/
theorem entireCovariance_eigenvector_iff (q : XiZeroCopy) (v : Space) :
    entireCovariance v = (entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹):ℂ) • v ↔
      nativeCovariance v = (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v := by
  exact cfc_eigenvector_iff_of_singleton_fibre nativeCovariance nativeCovariance_selfAdjoint
    entireCovarianceSymbol continuous_entireCovarianceSymbol.continuousOn _ _
    (fun x hx => entireCovarianceSymbol_fibre (q.1:ℂ).im (xi_divisor_support_im_ne_zero q.1) x
      (spectrum_nonneg_of_nonneg nativeCovariance_nonneg hx)) v

private theorem xiEntireTarget_native_range_iff (q : XiZeroCopy) :
    ((xiEntireTarget q).im=0 ∧ -1 ≤ (xiEntireTarget q).re) ↔ (q.1:ℂ).re=1/2 := by
  have hr : (xiSpectralPoint q).re=(q.1:ℂ).im := by simp [xiSpectralPoint]
  have hre : (xiSpectralPoint q).re ≠ 0 := by rw [hr]; exact xi_divisor_support_im_ne_zero q.1
  have hi : (xiSpectralPoint q).im=0 ↔ (q.1:ℂ).re=1/2 := by
    simp [xiSpectralPoint]
    constructor <;> intro h <;> linarith
  obtain ⟨hlo,hhi⟩ := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  unfold xiEntireTarget
  rw [← criticalCasimir_centered_argument]
  change _ ↔ _
  exact (critical_strip_range_iff (xiSpectralPoint q) hre hlo hhi).trans hi

/-- Any nonzero actual entire-domain eigenvector at a full Xi target forces
critical placement. Its native range bound is used as well as reality. -/
theorem critical_of_entire_eigenvector (q : XiZeroCopy) (v : entireOperator.domain)
    (hn : (v:Space) ≠ 0) (he : entireOperator v = xiEntireTarget q • (v:Space)) :
    (q.1:ℂ).re=1/2 := by
  apply (xiEntireTarget_native_range_iff q).mp
  have hi : (xiEntireTarget q).im=0 := by
    by_contra hi
    exact hn (eq_zero_of_apply_eq_smul entireOperator_selfAdjoint hi he)
  refine ⟨hi,?_⟩
  have hl := entireOperator_re_inner_lower v
  rw [he,inner_smul_left,inner_self_eq_norm_sq_to_K] at hl
  norm_num [Complex.mul_re,← Complex.ofReal_pow] at hl
  have hp : 0 < ‖(v:Space)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  nlinarith

private theorem target_covariance_inverse (q : XiZeroCopy) (hq : (q.1:ℂ).re=1/2) :
    2+xiEntireTarget q = ((entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹):ℝ):ℂ)⁻¹ := by
  have he := (xi_real_native_preimage_iff q (nativePartner (q.1:ℂ).im)).mpr ⟨hq,rfl⟩
  have hs := entireCovarianceSymbol_inverse ((xiNativeEigenvalue q)⁻¹)
    (inv_pos.mpr (xiNativeEigenvalue_pos q))
  have ha : ((xiNativeEigenvalue q)⁻¹)⁻¹-1=nativePartner (q.1:ℂ).im := by
    simp [xiNativeEigenvalue]
  rw [ha] at hs
  have him : (xiEntireTarget q).im=0 := by
    change (casimirTransform (((q.1:ℂ)/2)*(1-(q.1:ℂ)/2))).im=0
    rw [← he]
    exact (casimirTransform_real_range _).1
  apply Complex.ext
  · simp only [← Complex.ofReal_inv,Complex.add_re,Complex.ofReal_re]
    change 2+(xiEntireTarget q).re=(entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹))⁻¹
    change casimirTransform (nativePartner (q.1:ℂ).im)=xiEntireTarget q at he
    rw [he] at hs
    linarith
  · simp [← Complex.ofReal_inv,him]

private theorem covariance_residual_iff_of_critical (q : XiZeroCopy)
    (hq : (q.1:ℂ).re=1/2) (v : Space) :
    v-(2+xiEntireTarget q) • entireCovariance v=0 ↔
      nativeCovariance v=(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v := by
  rw [target_covariance_inverse q hq,← entireCovariance_eigenvector_iff]
  let c : ℂ := (entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹):ℝ)
  have hc : c≠0 := Complex.ofReal_ne_zero.mpr
    (entireCovarianceSymbol_pos (inv_pos.mpr (xiNativeEigenvalue_pos q))).ne'
  change v-c⁻¹ • entireCovariance v=0 ↔ entireCovariance v=c • v
  rw [sub_eq_zero]
  constructor
  · intro he
    have h : c • v=entireCovariance v := by
      conv_lhs => rw [he]
      rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
    exact h.symm
  · intro he
    rw [he,smul_smul,inv_mul_cancel₀ hc,one_smul]

/-- The full Xi residual has exactly the original covariance eigenspace on the
critical line and only the zero vector elsewhere. This classifies every vector,
without asserting that the nonzero eigenspace is occupied. -/
theorem covariance_residual_zero_iff (q : XiZeroCopy) (v : Space) :
    v-(2+xiEntireTarget q) • entireCovariance v=0 ↔
      v=0 ∨ ((q.1:ℂ).re=1/2 ∧ nativeCovariance v=(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v) := by
  constructor
  · intro he
    by_cases hv : v=0
    · exact Or.inl hv
    · have hn : entireCovariance v≠0 := fun h => hv (entireCovariance_injective
        (by simpa only [map_zero] using h))
      have hEig : entireOperator ⟨entireCovariance v,entireCovariance_mem_domain v⟩ =
          xiEntireTarget q • entireCovariance v := by
        rw [entireOperator_apply_covariance]
        rw [sub_eq_zero] at he
        linear_combination (norm := module) he
      have hq := critical_of_entire_eigenvector q _ hn hEig
      exact Or.inr ⟨hq,(covariance_residual_iff_of_critical q hq v).mp he⟩
  · rintro (rfl | ⟨hq,hv⟩)
    · simp
    · exact (covariance_residual_iff_of_critical q hq v).mpr hv

/-- The recovered covariance eigen-equation is exactly the native operator
eigen-equation on its original closed domain. -/
theorem covariance_native_eigenvector_iff (q : XiZeroCopy) (v : energyOperator.domain) :
    nativeCovariance (v:Space)=(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • (v:Space) ↔
      energyOperator v=(xiNativeEigenvalue q:ℂ) • (v:Space) := by
  have ha : xiNativeEigenvalue q≠0 := (xiNativeEigenvalue_pos q).ne'
  have hi : nativeCovariance (energyOperator v)=(v:Space) :=
    closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective v
  constructor
  · intro he
    apply nativeCovariance_injective
    rw [hi,map_smul,he,smul_smul,← Complex.ofReal_mul,mul_inv_cancel₀ ha]
    simp
  · intro he
    rw [he,map_smul] at hi
    have h := congrArg (fun w : Space => (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • w) hi
    simpa only [smul_smul,← Complex.ofReal_mul,inv_mul_cancel₀ ha,Complex.ofReal_one,one_smul] using h

open SelbergScatteringForcingTransport

/-- The full nonreal native resolvent commutes with the actual native covariance.
Both responses are identified using the original closed-domain inverse equations. -/
theorem sourceResolvent_nativeCovariance_commute (q : XiZeroCopy) (f : Space) :
    sourceResolvent q (nativeCovariance f)=nativeCovariance (sourceResolvent q f) := by
  let v := sourceResolvent q f
  have hb := closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective v
  have hR := sourceResolvent_equation q f
  have h := congrArg nativeCovariance hR
  have hi : nativeCovariance (energyOperator
      ⟨sourceResolvent q f,sourceResolvent_mem_domain q f⟩)=sourceResolvent q f :=
    closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective _
  rw [map_sub,map_smul,hi] at h
  have hEq : shiftedMap energyOperator (SelbergScatteringNativeResidual.scatteringEnergy (q.1:ℂ))
      ⟨nativeCovariance v,hb.1⟩ = nativeCovariance f := by
    rw [shiftedMap_apply]
    change closedDenseInverse nativeCovariance ⟨nativeCovariance v,hb.1⟩ -
      SelbergScatteringNativeResidual.scatteringEnergy (q.1:ℂ) • nativeCovariance v = _
    rw [hb.2]
    exact h
  have he := injective_shiftedMap energyOperator_selfAdjoint (scatteringEnergy_nonreal q)
    (a₁ := ⟨sourceResolvent q (nativeCovariance f),sourceResolvent_mem_domain q _⟩)
    (a₂ := ⟨nativeCovariance v,hb.1⟩)
    (by rw [shiftedMap_apply,sourceResolvent_equation,hEq])
  exact congrArg Subtype.val he

/-- Exact kernel of the full original forcing-to-entire-residual operator.
A nonzero forcing is annihilated precisely in the recovered native eigenspace
and only for critical Xi copies; there is no asserted occurrence. -/
theorem entireForcingTransport_zero_iff (q : XiZeroCopy) (f : Space) :
    entireForcingTransport q f=0 ↔
      f=0 ∨ ((q.1:ℂ).re=1/2 ∧ nativeCovariance f=(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • f) := by
  have hinj : Function.Injective (sourceResolvent q) :=
    resolventCLM_injective energyOperator_selfAdjoint (scatteringEnergy_nonreal q)
  have h0 : sourceResolvent q f=0 ↔ f=0 := by
    constructor
    · intro h
      exact hinj (by simpa only [map_zero] using h)
    · intro h
      rw [h,map_zero]
  have hEig : nativeCovariance (sourceResolvent q f)=
      (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • sourceResolvent q f ↔
      nativeCovariance f=(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • f := by
    rw [← sourceResolvent_nativeCovariance_commute,← map_smul]
    exact hinj.eq_iff
  rw [entireForcingTransport_apply,covariance_residual_zero_iff,h0,hEig]

end
end RHTower.SelbergScatteringEntireEigenvectors
