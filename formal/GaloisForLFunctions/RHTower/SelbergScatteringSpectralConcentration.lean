import GaloisForLFunctions.RHTower.SelbergScatteringEntireEigenvectors
import GaloisForLFunctions.HTGeometry.CfcApproximateKernel

/-!
# Recovery of native spectral concentration from the entire Xi operator

Equal continuous spectral fibres give equivalent bounded approximate kernels.
For the actual entire covariance, every unit approximate family at the full Xi
target forces critical placement and concentration at the unique original
native covariance value. Applying the original covariance and normalizing
produces actual native-domain unit vectors, with vanishing original operator
residual and norm distance tending to zero from the input family. This does
not produce the independent full-Xi approximate family required by SQB.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace
namespace RHTower.SelbergScatteringSpectralConcentration
open D4BMModularCore SelbergScatteringEntireOperator SelbergScatteringEntireTransform
open SelbergScatteringEntireXiPackets SelbergScatteringEntireEigenvectors
noncomputable section

/-- The entire covariance recovers exactly the original covariance concentration
for every bounded family, including at the spectral accumulation point zero. -/
theorem entireCovariance_residual_tendsto_iff
    {ι : Type*} {l : Filter ι} (q : XiZeroCopy) (v : ι → Space)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) :
    Tendsto (fun i => ‖entireCovariance (v i)-
      (entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹):ℂ) • v i‖) l (𝓝 0) ↔
    Tendsto (fun i => ‖nativeCovariance (v i)-
      (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v i‖) l (𝓝 0) :=
  cfc_residual_tendsto_zero_iff_of_singleton_fibre nativeCovariance nativeCovariance_selfAdjoint
    entireCovarianceSymbol continuous_entireCovarianceSymbol.continuousOn _ _
    (fun x hx => entireCovarianceSymbol_fibre (q.1:ℂ).im (xi_divisor_support_im_ne_zero q.1) x
      (spectrum_nonneg_of_nonneg nativeCovariance_nonneg hx)) v hM hv

/-- The original quadratic-form lower bound controls the real part of every
unit-domain residual, in addition to the self-adjoint imaginary-part bound. -/
theorem entire_unit_real_residual_lower (mu : ℂ) (v : entireOperator.domain)
    (hv : ‖(v:Space)‖=1) :
    -1-mu.re ≤ ‖entireOperator v-mu • (v:Space)‖ := by
  have hl := entireOperator_re_inner_lower v
  have hr : (inner ℂ (entireOperator v-mu • (v:Space)) (v:Space)).re ≤
      ‖entireOperator v-mu • (v:Space)‖ := by
    have hn := norm_inner_le_norm (𝕜 := ℂ) (entireOperator v-mu • (v:Space)) (v:Space)
    exact (Complex.re_le_norm _).trans (by simpa only [hv,mul_one] using hn)
  rw [inner_sub_left,inner_smul_left,inner_self_eq_norm_sq_to_K,hv] at hr
  simp only [hv,one_pow,Complex.sub_re,map_one,mul_one] at hl hr
  norm_num at hr
  linarith

/-- Any actual unit approximate family at a full Xi target forces critical
placement. All spectral reality and lower-range inputs are derived from the native operator. -/
theorem critical_of_entire_approximate (q : XiZeroCopy)
    (v : ℕ → entireOperator.domain) (hv : ∀ n, ‖(v n:Space)‖=1)
    (ht : Tendsto (fun n => ‖entireOperator (v n)-xiEntireTarget q • (v n:Space)‖)
      atTop (𝓝 0)) : (q.1:ℂ).re=1/2 := by
  have him : (xiEntireTarget q).im=0 := by
    have hl := ge_of_tendsto' ht (fun n => by
      simpa only [hv n,mul_one] using
        norm_sub_smul_lower_bound entireOperator_selfAdjoint (xiEntireTarget q) (v n))
    exact abs_eq_zero.mp (le_antisymm hl (abs_nonneg _))
  have hre : -1 ≤ (xiEntireTarget q).re := by
    have hl := ge_of_tendsto' ht (fun n => entire_unit_real_residual_lower (xiEntireTarget q) (v n) (hv n))
    linarith
  have hxre : (xiSpectralPoint q).re≠0 := by
    simpa [xiSpectralPoint] using xi_divisor_support_im_ne_zero q.1
  obtain ⟨hlo,hhi⟩ := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  have hp : (xiSpectralPoint q).im=0 :=
    (critical_strip_range_iff (xiSpectralPoint q) hxre hlo hhi).mp (by
      simp only [xiSpectralPoint,criticalCasimir_centered_argument]
      exact ⟨him,hre⟩)
  simp [xiSpectralPoint] at hp
  linarith

private theorem target_symbol_relation (q : XiZeroCopy) (hq : (q.1:ℂ).re=1/2) :
    (entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹):ℂ)*(2+xiEntireTarget q)=1 := by
  have he := (xi_real_native_preimage_iff q (nativePartner (q.1:ℂ).im)).mpr ⟨hq,rfl⟩
  have hs := entireCovarianceSymbol_inverse ((xiNativeEigenvalue q)⁻¹)
    (inv_pos.mpr (xiNativeEigenvalue_pos q))
  have ha : ((xiNativeEigenvalue q)⁻¹)⁻¹-1=nativePartner (q.1:ℂ).im := by
    simp [xiNativeEigenvalue]
  rw [ha] at hs
  change casimirTransform (nativePartner (q.1:ℂ).im)=xiEntireTarget q at he
  have him : (xiEntireTarget q).im=0 := by
    rw [← he]
    exact (casimirTransform_real_range _).1
  rw [he] at hs
  have hc := (entireCovarianceSymbol_pos (inv_pos.mpr (xiNativeEigenvalue_pos q))).ne'
  apply Complex.ext
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,
      zero_mul,sub_zero,Complex.one_re]
    change entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹)*(2+(xiEntireTarget q).re)=1
    have hd : 2+(xiEntireTarget q).re=(entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹))⁻¹ := by linarith
    rw [hd,mul_inv_cancel₀ hc]
  · simp [him]

/-- Every full-Xi entire approximate family concentrates in the unique original
native covariance fibre, with no source identification or domain assumption added. -/
theorem nativeCovariance_residual_of_entire_approximate (q : XiZeroCopy)
    (v : ℕ → entireOperator.domain) (hv : ∀ n, ‖(v n:Space)‖=1)
    (ht : Tendsto (fun n => ‖entireOperator (v n)-xiEntireTarget q • (v n:Space)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖nativeCovariance (v n:Space)-
      (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • (v n:Space)‖) atTop (𝓝 0) := by
  have hq := critical_of_entire_approximate q v hv ht
  let c : ℂ := (entireCovarianceSymbol ((xiNativeEigenvalue q)⁻¹):ℝ)
  have hc : c*(2+xiEntireTarget q)=1 := target_symbol_relation q hq
  have he (n : ℕ) : entireCovariance (v n:Space)-c • (v n:Space) =
      -c • entireCovariance (entireOperator (v n)-xiEntireTarget q • (v n:Space)) := by
    have hi := entireCovariance_apply_operator (v n)
    rw [map_add,map_smul] at hi
    rw [map_sub,map_smul,smul_sub,smul_smul]
    have hh := congrArg (fun w : Space => c • w) hi
    simp only [smul_add,smul_smul] at hh
    have hz : c*2+c*xiEntireTarget q=1 := by rw [← mul_add,hc]
    linear_combination (norm := module) hh - hz • entireCovariance (v n:Space)
  apply (entireCovariance_residual_tendsto_iff q (fun n => (v n:Space))
    (M := 1) (by norm_num) (fun n => (hv n).le)).mp
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => show ‖entireCovariance (v n:Space)-c • (v n:Space)‖ ≤
      (‖c‖*‖entireCovariance‖)*‖entireOperator (v n)-xiEntireTarget q • (v n:Space)‖ from ?_)
    (by simpa using ht.const_mul (‖c‖*‖entireCovariance‖))
  rw [he,norm_smul,norm_neg,mul_assoc]
  exact mul_le_mul_of_nonneg_left (entireCovariance.le_opNorm _) (norm_nonneg _)

/-- The covariance regularizes every vector into the actual native graph domain. -/
def nativeRecoveredDomain (v : Space) : energyOperator.domain :=
  ⟨nativeCovariance v,(closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective v).1⟩

theorem nativeRecoveredDomain_apply (v : Space) :
    energyOperator (nativeRecoveredDomain v)=v :=
  (closedDenseInverse_apply_C nativeCovariance nativeCovariance_injective v).2

/-- Exact native residual of the recovered graph vector, retaining the full
original covariance residual and its scalar coefficient. -/
theorem nativeRecoveredDomain_residual (q : XiZeroCopy) (v : Space) :
    energyOperator (nativeRecoveredDomain v)-
      (xiNativeEigenvalue q:ℂ) • (nativeRecoveredDomain v:Space) =
      -(xiNativeEigenvalue q:ℂ) •
        (nativeCovariance v-(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v) := by
  rw [nativeRecoveredDomain_apply]
  change v-(xiNativeEigenvalue q:ℂ) • nativeCovariance v= _
  rw [smul_sub,smul_smul,← Complex.ofReal_neg,← Complex.ofReal_mul,
    neg_mul,mul_inv_cancel₀ (xiNativeEigenvalue_pos q).ne']
  simp [sub_eq_add_neg,add_comm]

/-- Injectivity makes native covariance normalization legitimate for every
nonzero source vector. -/
theorem nativeCovariance_norm_pos {v : Space} (hv : v≠0) :
    0 < ‖nativeCovariance v‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hv (nativeCovariance_injective (by simpa only [map_zero] using h))

/-- A canonical actual native-domain unit vector recovered from a nonzero input. -/
def nativeRecoveredUnit (v : Space) : energyOperator.domain :=
  ((‖nativeCovariance v‖⁻¹:ℝ):ℂ) • nativeRecoveredDomain v

theorem nativeRecoveredUnit_norm {v : Space} (hv : v≠0) :
    ‖(nativeRecoveredUnit v:Space)‖=1 := by
  rw [nativeRecoveredUnit,Submodule.coe_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (nativeCovariance_norm_pos hv))]
  exact inv_mul_cancel₀ (nativeCovariance_norm_pos hv).ne'

/-- Exact normalized native residual; both scalar factors and the nonzero
normalization denominator remain explicit. -/
theorem nativeRecoveredUnit_residual_norm (q : XiZeroCopy) {v : Space} (hv : v≠0) :
    ‖energyOperator (nativeRecoveredUnit v)-
      (xiNativeEigenvalue q:ℂ) • (nativeRecoveredUnit v:Space)‖ =
      (‖nativeCovariance v‖⁻¹*xiNativeEigenvalue q)*
        ‖nativeCovariance v-(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v‖ := by
  rw [nativeRecoveredUnit,energyOperator.map_smul,Submodule.coe_smul,
    smul_comm (xiNativeEigenvalue q:ℂ),← smul_sub,norm_smul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (nativeCovariance_norm_pos hv)),
    nativeRecoveredDomain_residual,norm_smul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (xiNativeEigenvalue_pos q),mul_assoc]

/-- Unit covariance concentration fixes the normalization denominator at the
positive reciprocal of the native target energy. -/
theorem nativeCovariance_norm_tendsto_of_residual (q : XiZeroCopy)
    (v : ℕ → Space) (hv : ∀ n, ‖v n‖=1)
    (ht : Tendsto (fun n => ‖nativeCovariance (v n)-
      (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖nativeCovariance (v n)‖) atTop (𝓝 (xiNativeEigenvalue q)⁻¹) := by
  have hb : 0 < (xiNativeEigenvalue q)⁻¹ := inv_pos.mpr (xiNativeEigenvalue_pos q)
  have hs (n : ℕ) : ‖(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v n‖=(xiNativeEigenvalue q)⁻¹ := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb,hv n,mul_one]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with n hn
  calc
    dist ‖nativeCovariance (v n)‖ (xiNativeEigenvalue q)⁻¹ =
        |‖nativeCovariance (v n)‖-‖(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v n‖| := by
      rw [hs,Real.dist_eq]
    _ ≤ ‖nativeCovariance (v n)-(((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v n‖ :=
      abs_norm_sub_norm_le _ _
    _ < ε := by simpa only [dist_zero_right,norm_norm] using hn

/-- Native graph regularization recovers an approximate family for the original
operator from every full-Xi entire approximate family. -/
theorem nativeRecoveredUnit_residual_of_entire_approximate (q : XiZeroCopy)
    (v : ℕ → entireOperator.domain) (hv : ∀ n, ‖(v n:Space)‖=1)
    (ht : Tendsto (fun n => ‖entireOperator (v n)-xiEntireTarget q • (v n:Space)‖)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖energyOperator (nativeRecoveredUnit (v n:Space))-
      (xiNativeEigenvalue q:ℂ) • (nativeRecoveredUnit (v n:Space):Space)‖) atTop (𝓝 0) := by
  have hc := nativeCovariance_residual_of_entire_approximate q v hv ht
  have hn := nativeCovariance_norm_tendsto_of_residual q (fun n => (v n:Space)) hv hc
  have hi := hn.inv₀ (inv_ne_zero (xiNativeEigenvalue_pos q).ne')
  have hnz (n : ℕ) : (v n:Space)≠0 := by
    intro h
    have h1 := hv n
    rw [h,norm_zero] at h1
    exact zero_ne_one h1
  simp_rw [nativeRecoveredUnit_residual_norm q (hnz _)]
  simpa using (hi.mul_const (xiNativeEigenvalue q)).mul hc

/-- Native graph regularization of a unit concentrating family changes its
vectors by a norm error tending to zero. This retains the full input family. -/
theorem nativeRecoveredUnit_sub_tendsto_of_residual (q : XiZeroCopy)
    (v : ℕ → Space) (hv : ∀ n, ‖v n‖=1)
    (ht : Tendsto (fun n => ‖nativeCovariance (v n)-
      (((xiNativeEigenvalue q)⁻¹:ℝ):ℂ) • v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(nativeRecoveredUnit (v n):Space)-v n‖) atTop (𝓝 0) := by
  let b : ℝ := (xiNativeEigenvalue q)⁻¹
  have hb : b≠0 := inv_ne_zero (xiNativeEigenvalue_pos q).ne'
  have hn := nativeCovariance_norm_tendsto_of_residual q v hv ht
  have hi : Tendsto (fun n => ‖nativeCovariance (v n)‖⁻¹) atTop (𝓝 b⁻¹) := hn.inv₀ hb
  have hz : Tendsto (fun n => |‖nativeCovariance (v n)‖⁻¹*b-1|) atTop (𝓝 0) := by
    simpa only [inv_mul_cancel₀ hb,sub_self,abs_zero] using ((hi.mul_const b).sub_const 1).abs
  have hh : Tendsto (fun n => ‖nativeCovariance (v n)‖⁻¹*
      ‖nativeCovariance (v n)-(b:ℂ) • v n‖+|‖nativeCovariance (v n)‖⁻¹*b-1|) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hi.mul ht).add hz
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hh
  have he : (nativeRecoveredUnit (v n):Space)-v n =
      ((‖nativeCovariance (v n)‖⁻¹:ℝ):ℂ) • (nativeCovariance (v n)-(b:ℂ) • v n)+
      ((‖nativeCovariance (v n)‖⁻¹*b-1:ℝ):ℂ) • v n := by
    change ((‖nativeCovariance (v n)‖⁻¹:ℝ):ℂ) • nativeCovariance (v n)-v n= _
    push_cast
    module
  calc
    _ ≤ ‖((‖nativeCovariance (v n)‖⁻¹:ℝ):ℂ) • (nativeCovariance (v n)-(b:ℂ) • v n)‖+
        ‖((‖nativeCovariance (v n)‖⁻¹*b-1:ℝ):ℂ) • v n‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = _ := by
      rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hv n,mul_one]

end
end RHTower.SelbergScatteringSpectralConcentration
