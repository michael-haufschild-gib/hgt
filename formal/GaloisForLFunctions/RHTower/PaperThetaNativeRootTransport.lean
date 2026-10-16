import GaloisForLFunctions.RHTower.PaperThetaNativeQuantileComparison
import GaloisForLFunctions.RHTower.PaperThetaNativeGrushin
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceConormalSocle
import Mathlib.Tactic.Module

/-! # All generalized native modes enter the full theta source block

The native-to-source comparison transports every pencil power. Its constant
kernel is disjoint from each actual Xi root block, giving an injection of the
whole native generalized-root space into the multiplicity-exact Hilbert block.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Module.End
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem nativeCompactResolvent_constant (c : ℂ) :
    nativeCompactResolvent (nativeConstantCLM c) = nativeConstantCLM (I*c) := by
  symm
  apply boundedNativeResolvent_unique nativeCompactParameter (nativeConstantCLM c)
    (nativeConstantCLM (I*c)) (I*c) (differentiable_const (I*c)) tendsto_const_nhds
  intro x
  change deriv (fun _ : ℝ => I*c) x+sourceLogDerivative x*(I*c-I*c)+
    I*nativeCompactParameter.val*(I*c) = -I*c
  rw [deriv_const, sub_self, mul_zero, zero_add, zero_add, nativeCompactParameter_val]
  rw [← pow_two I, Complex.I_sq]
  ring

theorem nativeSourceComparison_constant (c : ℂ) :
    nativeSourceComparison (nativeConstantCLM c) = 0 := by
  have h := thetaKernel_native_source_identity (nativeConstantCLM c)
  have hv : nativeConstantCLM c+I • nativeCompactResolvent (nativeConstantCLM c) = 0 := by
    rw [nativeCompactResolvent_constant]
    ext x
    change c+I*(I*c) = 0
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hv, map_zero, map_zero] at h
  exact neg_eq_zero.mp h.symm

theorem nativeSourceComparison_kernel :
    LinearMap.ker nativeSourceComparison.toLinearMap = LinearMap.range nativeConstantCLM.toLinearMap := by
  apply le_antisymm
  · intro v hv
    change nativeSourceComparison v = 0 at hv
    have hr : boundedNativeResidual nativeCompactParameter v = 0 :=
      nativeQuantileMap_injective (by simpa only [map_zero] using hv)
    let t := boundedResolventTrace nativeCompactParameter v
    have hk : nativeCompactResolvent v = nativeConstantCLM t := by
      ext x
      have he := congrArg (fun f : NativeContinuousSpace => f x) hr
      change nativeCompactResolvent v x-t = 0 at he
      exact sub_eq_zero.mp he
    refine ⟨-I*t, ?_⟩
    apply BoundedContinuousFunction.ext
    intro x
    have he := boundedNativeResolvent_ode nativeCompactParameter v x
    change deriv (nativeCompactResolvent v) x+
      sourceLogDerivative x*(nativeCompactResolvent v x-t)+
      I*nativeCompactParameter.val*nativeCompactResolvent v x = -I*v x at he
    rw [hk, nativeCompactParameter_val] at he
    change deriv (fun _ : ℝ => t) x+sourceLogDerivative x*(t-t)+I*I*t = -I*v x at he
    rw [deriv_const, sub_self, mul_zero, zero_add, zero_add] at he
    change -I*t = v x
    linear_combination (norm := ring_nf) I*he
    simp only [pow_succ, Complex.I_sq]
    ring
  · rintro v ⟨c,rfl⟩
    exact nativeSourceComparison_constant c

theorem nativeSourceComparison_eq_zero_on_root {mu : ℂ} (hmu : mu ≠ I)
    {v : NativeContinuousSpace}
    (hv : v ∈ maxGenEigenspace nativeCompactResolvent.toLinearMap mu)
    (hJ : nativeSourceComparison v = 0) : v = 0 := by
  obtain ⟨c,hc⟩ := nativeSourceComparison_kernel.le hJ
  change nativeConstantCLM c = v at hc
  have hk : nativeCompactResolvent v = I • v := by
    rw [← hc, nativeCompactResolvent_constant]
    rfl
  by_contra hv0
  have hev : HasEigenvector (nativeCompactResolvent.toLinearMap-mu • 1) (I-mu) v := by
    refine ⟨mem_eigenspace_iff.mpr ?_,hv0⟩
    change nativeCompactResolvent v-mu • v = (I-mu) • v
    rw [hk, sub_smul]
  obtain ⟨n,hn⟩ := (mem_maxGenEigenspace _ _ _).mp hv
  rw [hev.pow_apply n] at hn
  exact (smul_ne_zero (pow_ne_zero n (sub_ne_zero.mpr hmu.symm)) hv0) hn

/-- Polynomial pencil transport on the whole native space, at every parameter. -/
theorem nativeSourceComparison_pencil (z : ℂ) (v : NativeContinuousSpace) :
    thetaSourcePencil z (nativeSourceComparison v) =
      thetaSourcePencil I (nativeSourceComparison (nativePencil z v)) := by
  have he := nativeSourceComparison_intertwining v
  change nativeSourceComparison v+z • thetaKernelOperator (nativeSourceComparison v) = _
  change _ = nativeSourceComparison (v+(I-z) • nativeCompactResolvent v)+
    I • thetaKernelOperator (nativeSourceComparison (v+(I-z) • nativeCompactResolvent v))
  rw [map_add, map_smul, map_add, map_smul]
  calc
    _ = nativeSourceComparison v+I • thetaKernelOperator (nativeSourceComparison v)+
        (I-z) • (-thetaKernelOperator (nativeSourceComparison v)) := by module
    _ = nativeSourceComparison v+I • thetaKernelOperator (nativeSourceComparison v)+
        (I-z) • (nativeSourceComparison (nativeCompactResolvent v)+
          I • thetaKernelOperator (nativeSourceComparison (nativeCompactResolvent v))) := by rw [he]
    _ = _ := by module

private theorem thetaPencils_commute (z : ℂ) :
    Commute (thetaSourcePencil z).toLinearMap (thetaSourcePencil I).toLinearMap := by
  apply LinearMap.ext
  intro v
  change thetaSourcePencil z (thetaSourcePencil I v) =
    thetaSourcePencil I (thetaSourcePencil z v)
  simp only [thetaSourcePencil, _root_.add_apply, one_apply_eq_self,
    _root_.smul_apply, map_add, map_smul]
  module

theorem nativeSourceComparison_pencil_power_kernel (z : ℂ) (n : ℕ)
    (v : NativeContinuousSpace) (hv : ((nativePencil z).toLinearMap ^ n) v = 0) :
    ((thetaSourcePencil z).toLinearMap ^ n) (nativeSourceComparison v) = 0 := by
  induction n generalizing v with
  | zero => simpa only [pow_zero, Module.End.one_apply, map_zero] using congrArg nativeSourceComparison hv
  | succ n ih =>
      have hc := congrArg (fun T : Module.End ℂ NativeQuantileSpace =>
        T (nativeSourceComparison (nativePencil z v))) ((thetaPencils_commute z).pow_left n).eq
      rw [pow_succ]
      change ((thetaSourcePencil z).toLinearMap ^ n)
        (thetaSourcePencil z (nativeSourceComparison v)) = 0
      rw [nativeSourceComparison_pencil]
      change ((thetaSourcePencil z).toLinearMap ^ n)
          (thetaSourcePencil I (nativeSourceComparison (nativePencil z v))) = _
      rw [show ((thetaSourcePencil z).toLinearMap ^ n)
          (thetaSourcePencil I (nativeSourceComparison (nativePencil z v))) =
          thetaSourcePencil I (((thetaSourcePencil z).toLinearMap ^ n)
            (nativeSourceComparison (nativePencil z v))) from hc]
      have hprev : ((nativePencil z).toLinearMap ^ n) (nativePencil z v) = 0 := by
        rw [pow_succ, Module.End.mul_apply] at hv
        exact hv
      rw [ih (nativePencil z v) hprev, map_zero]

def nativeXiResolventValue (rho : XiDivisorSupport) : ℂ :=
  (xiSpectralPointSupport rho-I)⁻¹

theorem xiSpectralPointSupport_sub_I_ne_zero (rho : XiDivisorSupport) :
    xiSpectralPointSupport rho-I ≠ 0 := by
  intro h
  have hr : (xiSpectralPointSupport rho).re ≠ 0 := by
    simpa [xiSpectralPointSupport, mul_re] using xi_divisor_support_im_ne_zero rho
  apply hr
  have hh := congrArg Complex.re (sub_eq_zero.mp h)
  simpa using hh

theorem nativeXiResolventValue_ne_I (rho : XiDivisorSupport) :
    nativeXiResolventValue rho ≠ I := by
  intro h
  have hp := mul_inv_cancel₀ (xiSpectralPointSupport_sub_I_ne_zero rho)
  change (xiSpectralPointSupport rho-I)*nativeXiResolventValue rho = 1 at hp
  rw [h] at hp
  have hz : xiSpectralPointSupport rho = 0 := by
    linear_combination (norm := ring_nf) -I*hp
    simp only [pow_succ, Complex.I_sq]
    ring
  exact XiC_zero_ne (hz ▸ XiC_xiSpectralPointSupport_eq_zero rho)

abbrev NativeXiRootBlock (rho : XiDivisorSupport) :=
  maxGenEigenspace nativeCompactResolvent.toLinearMap (nativeXiResolventValue rho)

theorem nativeSourceComparison_mem_root (rho : XiDivisorSupport)
    {v : NativeContinuousSpace} (hv : v ∈ NativeXiRootBlock rho) :
    nativeSourceComparison v ∈ ThetaRootBlock (thetaSpectrumOfXiSupport rho) := by
  let z := xiSpectralPointSupport rho
  have hz : z ≠ 0 := fun h => XiC_zero_ne (h ▸ XiC_xiSpectralPointSupport_eq_zero rho)
  have hs : (I-z)*nativeXiResolventValue rho = -1 := by
    rw [nativeXiResolventValue, show I-z = -(z-I) from by ring, neg_mul,
      mul_inv_cancel₀ (xiSpectralPointSupport_sub_I_ne_zero rho)]
  have hG : (nativePencil z).toLinearMap =
      (I-z) • (nativeCompactResolvent.toLinearMap-nativeXiResolventValue rho • 1) := by
    apply LinearMap.ext
    intro u
    change u+(I-z) • nativeCompactResolvent u =
      (I-z) • (nativeCompactResolvent u-nativeXiResolventValue rho • u)
    rw [smul_sub, smul_smul, hs, neg_one_smul]
    abel
  have hF : (thetaSourcePencil z).toLinearMap =
      z • (thetaKernelOperator.toLinearMap-(-z⁻¹) • 1) := by
    apply LinearMap.ext
    intro u
    change u+z • thetaKernelOperator u = z • (thetaKernelOperator u-(-z⁻¹) • u)
    rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ hz, neg_one_smul]
    abel
  obtain ⟨n,hn⟩ := (mem_maxGenEigenspace _ _ _).mp hv
  have hGn : ((nativePencil z).toLinearMap ^ n) v = 0 := by
    rw [hG, smul_pow, LinearMap.smul_apply, hn, smul_zero]
  have hFn := nativeSourceComparison_pencil_power_kernel z n v hGn
  rw [hF, smul_pow, LinearMap.smul_apply] at hFn
  exact (mem_maxGenEigenspace _ _ _).mpr
    ⟨n,(smul_eq_zero.mp hFn).resolve_left (pow_ne_zero n hz)⟩

/-- Injection of every actual native generalized mode into the full source block. -/
def nativeSourceRootMap (rho : XiDivisorSupport) :
    NativeXiRootBlock rho →ₗ[ℂ] ThetaRootBlock (thetaSpectrumOfXiSupport rho) where
  toFun v := ⟨nativeSourceComparison v,nativeSourceComparison_mem_root rho v.property⟩
  map_add' v w := Subtype.ext (map_add nativeSourceComparison v.val w.val)
  map_smul' c v := Subtype.ext (map_smul nativeSourceComparison c v.val)

theorem nativeSourceRootMap_injective (rho : XiDivisorSupport) :
    Function.Injective (nativeSourceRootMap rho) := by
  intro v w hvw
  have he : nativeSourceComparison (v.val-w.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hvw)
  exact Subtype.ext (sub_eq_zero.mp (nativeSourceComparison_eq_zero_on_root
    (nativeXiResolventValue_ne_I rho) ((NativeXiRootBlock rho).sub_mem v.property w.property) he))

instance nativeXiRootBlock_finiteDimensional (rho : XiDivisorSupport) :
    FiniteDimensional ℂ (NativeXiRootBlock rho) :=
  FiniteDimensional.of_injective (nativeSourceRootMap rho) (nativeSourceRootMap_injective rho)

theorem finrank_nativeXiRootBlock_le (rho : XiDivisorSupport) :
    Module.finrank ℂ (NativeXiRootBlock rho) ≤ xiSupportMultiplicity rho := by
  rw [← finrank_thetaRootBlock_at_XiSupport rho]
  exact LinearMap.finrank_le_finrank_of_injective (nativeSourceRootMap_injective rho)

end RHTower.PaperThetaEndpoint
