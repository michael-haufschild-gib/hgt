import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCircleGreen
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalSourceAdjoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGoursat

/-! Reconstruction of the full angular and onset kernels from the literal theta source. -/
namespace RHTower.D4BMFullAngularReconstruction
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open D4BMCausalSourceKernel D4BMFullAngularCircle
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def kernelFlux (nu : ℂ) (z : ℝ) : ℝ :=
  (((z:ℂ)^(2 : ℕ)-1)*star (legendreKernel nu z)*legendreKernelFirst nu z).im

private theorem kernelFlux_derivative (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (kernelFlux nu) ((nu*(nu+1)).im*Complex.normSq (legendreKernel nu z)) z := by
  obtain ⟨hP,hP1⟩ := legendreKernel_derivatives nu hz
  have hzD := ((hasDerivAt_id z).ofReal_comp.pow 2).sub_const (1:ℂ)
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt z ((hzD.mul hP.star).mul hP1)
  apply h.congr_deriv
  norm_num only [Complex.imCLM_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  simp only [pow_one, Complex.ofReal_one, mul_one]
  change ((2*(z:ℂ)*star (legendreKernel nu z)+((z:ℂ)^(2 : ℕ)-1)*star (legendreKernelFirst nu z))*legendreKernelFirst nu z
    +((z:ℂ)^(2 : ℕ)-1)*star (legendreKernel nu z)*legendreKernelSecond nu z).im =
    (nu*(nu+1)).im*Complex.normSq (legendreKernel nu z)
  have he := congrArg (fun w : ℂ => (star (legendreKernel nu z)*w).im)
    (legendreKernel_equation nu hz)
  simp only [pow_two, Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,Complex.zero_re,Complex.zero_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply] at he ⊢
  linear_combination he

private theorem kernel_continuousOn (nu : ℂ) {Z : ℝ} :
    ContinuousOn (legendreKernel nu) (Icc 1 Z) := by
  intro z hz
  exact (legendreKernel_derivatives nu (lt_of_lt_of_le zero_lt_one hz.1)).1.continuousAt.continuousWithinAt

private theorem kernelFlux_integral (nu : ℂ) {Z : ℝ} (hZ : 1 ≤ Z) :
    kernelFlux nu Z=(nu*(nu+1)).im*∫ z in (1:ℝ)..Z, Complex.normSq (legendreKernel nu z) := by
  have hc : ContinuousOn (kernelFlux nu) (Icc 1 Z) := fun z hz =>
    (kernelFlux_derivative nu (lt_of_lt_of_le zero_lt_one hz.1)).continuousAt.continuousWithinAt
  have hn : ContinuousOn (fun z => Complex.normSq (legendreKernel nu z)) (Icc 1 Z) :=
    Complex.continuous_normSq.comp_continuousOn (kernel_continuousOn nu)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hZ hc
    (fun z hz => kernelFlux_derivative nu (lt_trans zero_lt_one hz.1))
    ((continuousOn_const.mul hn).intervalIntegrable_of_Icc hZ)
  have hzero : kernelFlux nu 1=0 := by simp [kernelFlux]
  rw [hzero,sub_zero,intervalIntegral.integral_const_mul] at hi
  exact hi.symm

private theorem kernel_ne_zero (nu : ℂ) (ha : (nu*(nu+1)).im ≠ 0)
    {Z : ℝ} (hZ : 1 ≤ Z) : legendreKernel nu Z ≠ 0 := by
  by_cases he : Z=1
  · rw [he,legendreKernel_one]
    exact one_ne_zero
  have hZ' : 1 < Z := lt_of_le_of_ne hZ (Ne.symm he)
  intro hzero
  have hf := kernelFlux_integral nu hZ
  have hz : kernelFlux nu Z=0 := by simp [kernelFlux,hzero]
  rw [hz] at hf
  have hn : ContinuousOn (fun z => Complex.normSq (legendreKernel nu z)) (Icc 1 Z) :=
    Complex.continuous_normSq.comp_continuousOn (kernel_continuousOn nu)
  have hp : 0 < ∫ z in (1:ℝ)..Z, Complex.normSq (legendreKernel nu z) := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hZ'
      (f := fun _ => (0:ℝ)) continuousOn_const hn
      (fun z _ => Complex.normSq_nonneg _)
      ⟨1,⟨le_rfl,hZ⟩,by simp [legendreKernel_one]⟩
    simpa using h
  exact mul_ne_zero ha (ne_of_gt hp) hf.symm

/-- The actual radial Legendre kernel is smooth through every real radius. -/
theorem radialLegendre_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiff ℝ ∞ (radialLegendre q branch) := by
  apply contDiff_iff_contDiffAt.mpr
  intro d
  exact (legendre_contDiffAt (2*physicalRate q branch+1) (Real.cosh_pos d)).comp d
    Real.contDiff_cosh.contDiffAt

/-- The physical angular parameter proves nonvanishing of the original Legendre kernel,
without a critical-line assumption or an additional angular-response premise. -/
theorem radialLegendre_ne_zero (q : XiZeroCopy) (branch : Bool) (d : ℝ) :
    radialLegendre q branch d ≠ 0 := by
  apply kernel_ne_zero (2*physicalRate q branch+1) _ (Real.one_le_cosh d)
  have he : (2*physicalRate q branch+1)*(2*physicalRate q branch+1+1)=parameter q branch := by
    rw [parameter_physicalRate]
    dsimp [D4BMQuadraticMixedSource.resolventParameter]
    ring
  rw [he]
  cases branch
  · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).2
  · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).1

/-- The source-only variation density. Its apparent singularity at radius zero is
integrable; no unknown full angular response occurs in this definition. -/
def sourceDensity (q : XiZeroCopy) (branch : Bool) (d x k : ℝ) : ℂ :=
  (parameter q branch*∫ a in (0:ℝ)..d,
    (Real.sinh a:ℂ)*radialLegendre q branch a*D4BMNativeCircle.mean q a x k)/
      ((Real.sinh d:ℂ)*radialLegendre q branch d^(2 : ℕ))

private theorem quotient_smooth (q : XiZeroCopy) (branch : Bool) (x k : ℝ) :
    ContDiff ℝ ∞ (fun d => angularMean q branch d x k/radialLegendre q branch d) := by
  simpa only [div_eq_mul_inv, Pi.inv_apply] using! (angularMean_smooth q branch x k).mul
    ((radialLegendre_smooth q branch).inv (radialLegendre_ne_zero q branch))

private theorem quotient_hasDerivAt (q : XiZeroCopy) (branch : Bool) (x k d : ℝ)
    (hd : 0 < d) :
    HasDerivAt (fun r => angularMean q branch r x k/radialLegendre q branch r)
      (sourceDensity q branch d x k) d := by
  have hm := ((angularMean_smooth q branch x k).differentiable (by simp) d).hasDerivAt
  have hp := ((radialLegendre_smooth q branch).differentiable (by simp) d).hasDerivAt
  have hpn := radialLegendre_ne_zero q branch d
  have hs : (Real.sinh d:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr (ne_of_gt hd))
  have hw := greenCurrent_finite_integral q branch x k d hd.le
  dsimp only [greenCurrent] at hw
  apply (hm.fun_div hp hpn).congr_deriv
  change (deriv (fun r => angularMean q branch r x k) d*radialLegendre q branch d-
      angularMean q branch d x k*deriv (radialLegendre q branch) d)/radialLegendre q branch d^(2 : ℕ)=_
  calc
    _ = ((Real.sinh d:ℂ)*(radialLegendre q branch d*deriv (fun r => angularMean q branch r x k) d-
        deriv (radialLegendre q branch) d*angularMean q branch d x k))/
        ((Real.sinh d:ℂ)*radialLegendre q branch d^(2 : ℕ)) := by field_simp [hs,hpn]
    _ = sourceDensity q branch d x k := by rw [hw]; rfl

/-- The source-only density is admitted by the actual integral, including the origin. -/
theorem sourceDensity_intervalIntegrable (q : XiZeroCopy) (branch : Bool) (x k D : ℝ)
    (hD : 0 ≤ D) : IntervalIntegrable (fun d => sourceDensity q branch d x k) volume 0 D := by
  have hc := (contDiff_infty_iff_deriv.mp (quotient_smooth q branch x k)).2.continuous
  apply (hc.intervalIntegrable (μ := volume) 0 D).congr_uIoo
  intro d hd
  have hd' : d ∈ Ioo 0 D := by simpa only [uIoo_of_le hD] using hd
  exact (quotient_hasDerivAt q branch x k d hd'.1).deriv

/-- The original full angular mean is recovered from its actual zero-radius datum and
the literal theta source, by a nonvanishing physical Legendre kernel. -/
theorem angularMean_reconstruction (q : XiZeroCopy) (branch : Bool) (x k D : ℝ)
    (hD : 0 ≤ D) :
    angularMean q branch D x k=radialLegendre q branch D*
      (fullAngularField q branch ![x,Real.exp k]+∫ d in (0:ℝ)..D, sourceDensity q branch d x k) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hD
    (quotient_smooth q branch x k).continuous.continuousOn
    (fun d hd => quotient_hasDerivAt q branch x k d hd.1)
    (sourceDensity_intervalIntegrable q branch x k D hD)
  have hzero : angularMean q branch 0 x k/radialLegendre q branch 0=
      fullAngularField q branch ![x,Real.exp k] := by
    simp [radialLegendre,legendreKernel_one,angularMean_zero]
  rw [hzero] at hi
  have he : angularMean q branch D x k/radialLegendre q branch D=
      fullAngularField q branch ![x,Real.exp k]+∫ d in (0:ℝ)..D, sourceDensity q branch d x k := by
    linear_combination -hi
  rw [div_eq_iff (radialLegendre_ne_zero q branch D)] at he
  rw [he,mul_comm]

/-- The forced part of the full angular mean, defined only from the literal source. -/
def sourceCorrection (q : XiZeroCopy) (branch : Bool) (D x k : ℝ) : ℂ :=
  radialLegendre q branch D*∫ d in (0:ℝ)..D, sourceDensity q branch d x k

/-- The original Legendre kernel with both original causal gates and the image factor. -/
def homogeneousDirichletKernel (q : XiZeroCopy) (branch : Bool) (h x y : ℝ) : ℂ :=
  ((if |x-y| ≤ h then riemannKernel (2*physicalRate q branch+1) h x y else 0)-
    (if |x+y| ≤ h then riemannKernel (2*physicalRate q branch+1) h x (-y) else 0))/2

/-- Direct and image circular averages of the original full angular field. -/
def angularDirichletKernel (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  ((if |x-y| ≤ h then angularMean q branch (Real.arcosh (invariant h x y)) X k else 0)-
    (if |x+y| ≤ h then angularMean q branch (Real.arcosh (invariant h x (-y))) X k else 0))/2

/-- The literal-source correction with the unchanged causal gates and reflected image. -/
def sourceDirichletCorrection (q : XiZeroCopy) (branch : Bool) (h x y X k : ℝ) : ℂ :=
  ((if |x-y| ≤ h then sourceCorrection q branch (Real.arcosh (invariant h x y)) X k else 0)-
    (if |x+y| ≤ h then sourceCorrection q branch (Real.arcosh (invariant h x (-y))) X k else 0))/2

private theorem causal_angular_reconstruction (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) (hc : |x-y| ≤ h) :
    angularMean q branch (Real.arcosh (invariant h x y)) X k=
      riemannKernel (2*physicalRate q branch+1) h x y*fullAngularField q branch ![X,Real.exp k]+
      sourceCorrection q branch (Real.arcosh (invariant h x y)) X k := by
  have hz := invariant_causal ⟨h,x,y,hc⟩
  have hp : radialLegendre q branch (Real.arcosh (invariant h x y))=
      riemannKernel (2*physicalRate q branch+1) h x y := by
    simp only [radialLegendre,riemannKernel,Real.cosh_arcosh hz]
  rw [angularMean_reconstruction q branch X k _ (Real.arcosh_nonneg hz)]
  dsimp only [sourceCorrection]
  rw [hp]
  ring

/-- Exact recovery of the full angular circular kernel inside its original direct/image support. -/
theorem angularDirichletKernel_reconstruction (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) :
    angularDirichletKernel q branch h x y X k=
      homogeneousDirichletKernel q branch h x y*fullAngularField q branch ![X,Real.exp k]+
      sourceDirichletCorrection q branch h x y X k := by
  dsimp only [angularDirichletKernel,homogeneousDirichletKernel,sourceDirichletCorrection]
  by_cases hd : |x-y| ≤ h <;> by_cases hi : |x+y| ≤ h
  · simp only [if_pos hd,if_pos hi]
    rw [causal_angular_reconstruction q branch h x y X k hd,
      causal_angular_reconstruction q branch h x (-y) X k (by simpa using hi)]
    ring
  · simp only [if_pos hd,if_neg hi]
    rw [causal_angular_reconstruction q branch h x y X k hd]
    ring
  · simp only [if_neg hd,if_pos hi]
    rw [causal_angular_reconstruction q branch h x (-y) X k (by simpa using hi)]
    ring
  · simp only [if_neg hd,if_neg hi]
    ring

/-- Direct and image circular averages of the original unprojected onset pulse. -/
def onsetDirichletKernel (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t h x y X k : ℝ) : ℂ :=
  ((if |x-y| ≤ h then onsetAngularMean q branch a τ t (Real.arcosh (invariant h x y)) X k else 0)-
    (if |x+y| ≤ h then onsetAngularMean q branch a τ t (Real.arcosh (invariant h x (-y))) X k else 0))/2

/-- The unchanged pulse's circular kernel is reconstructed with its full characteristic
datum, the source-only nested correction, and the original native theta-source kernel. -/
theorem onsetDirichletKernel_reconstruction (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t h x y X k : ℝ) :
    onsetDirichletKernel q branch a τ t h x y X k=
      onsetResponseCoefficient q branch a τ t*homogeneousDirichletKernel q branch h x y*
        fullAngularField q branch ![X,Real.exp k]+
      onsetResponseCoefficient q branch a τ t*sourceDirichletCorrection q branch h x y X k+
      onsetSourceCoefficient q branch a τ t*D4BMNativeCircle.nativeDirichletCausalKernel q h x y X k := by
  have he : onsetDirichletKernel q branch a τ t h x y X k=
      onsetResponseCoefficient q branch a τ t*angularDirichletKernel q branch h x y X k+
      onsetSourceCoefficient q branch a τ t*D4BMNativeCircle.nativeDirichletCausalKernel q h x y X k := by
    dsimp only [onsetDirichletKernel,angularDirichletKernel,D4BMNativeCircle.nativeDirichletCausalKernel,
      D4BMNativeCircle.nativeRiemannKernel,D4BMNativeCircle.angularKernel]
    by_cases hd : |x-y| ≤ h <;> by_cases hi : |x+y| ≤ h <;>
      simp only [hd,hi,↓reduceIte,onsetAngularMean_eq] <;> ring
  rw [he,angularDirichletKernel_reconstruction]
  ring

end
end RHTower.D4BMFullAngularReconstruction
