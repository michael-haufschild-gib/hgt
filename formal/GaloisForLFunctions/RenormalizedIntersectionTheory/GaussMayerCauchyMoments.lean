import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerQuadraticCone
import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwining

/-! The normalized Cauchy transform preserves the two zeta axes. Its
zeroth and spectral Mellin moments are both one, with absolute convergence. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyMoments

private def parameter (w : ℂ) (hw : 2 < w.re) :
    _root_.RHTower.D4BMEisensteinAbsoluteConvergenceParameter where
  s := (w+2)/2
  re_gt_one := by norm_num [Complex.div_re]; linarith only [hw]

private theorem weight_kernel {w : ℂ} (hw : 2 < w.re) :
    cauchyWeight w=_root_.RHTower.d4BMCauchyPowerKernel
      MayerScatteringNormalization.basePoint (parameter w hw).s := by
  funext v
  simp only [cauchyWeight,_root_.RHTower.d4BMCauchyPowerKernel,
    MayerScatteringNormalization.basePoint,parameter,one_pow]

/-- Absolute integrability of the Cauchy weight on the whole real line. -/
theorem cauchyWeight_integrable {w : ℂ} (hw : 2 < w.re) : Integrable (cauchyWeight w) := by
  rw [weight_kernel hw]
  exact _root_.RHTower.integrable_d4BMCauchyPowerKernel
    MayerScatteringNormalization.basePoint (parameter w hw)

/-- The positive half-line Cauchy integral is exactly the averaging normalization. -/
theorem cauchyWeight_integral {w : ℂ} (hw : 2 < w.re) :
    (∫ t in Ioi (0 : ℝ), cauchyWeight w t)=averagingFactor w := by
  have h := MayerScatteringNormalization.kernel_normalization (parameter w hw)
  rw [← weight_kernel hw] at h
  have hi : (∫ t : ℝ, cauchyWeight w t)=
      MayerScatteringNormalization.archimedeanFactor ((w+2)/2) := by
    simpa [Real.fourier_eq,parameter] using! h
  have he := _root_.RHTower.integral_eq_two_mul_integral_Ioi_of_even
    (cauchyWeight_integrable hw) (fun t => by simp only [cauchyWeight,neg_sq])
  unfold averagingFactor
  linear_combination (hi-he)/2

private theorem reciprocal_weight {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ)^(-2 : ℂ)*cauchyWeight w t⁻¹=(t : ℂ)^w*cauchyWeight w t := by
  have hn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have he : (1+(t⁻¹)^2)*t^2=1+t^2 := by
    field_simp [ht.ne']
    ring
  have hp := congrArg (fun x : ℝ => (x : ℂ)^(-((w+2)/2))) he
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg
    (by positivity : 0 ≤ 1+(t⁻¹)^2) (sq_nonneg t)] at hp
  have hs : ((t^2 : ℝ) : ℂ)^(-((w+2)/2))=(t : ℂ)^(-(w+2)) := by
    have h := Complex.cpow_mul_ofReal_nonneg ht.le (2 : ℝ) (-((w+2)/2))
    rw [show t^(2 : ℝ)=t^2 from Real.rpow_natCast t 2] at h
    have hc : ((2 : ℝ) : ℂ)*(-((w+2)/2))= -(w+2) := by push_cast; ring
    simpa only [hc] using h.symm
  rw [hs] at hp
  change (t : ℂ)^(-2 : ℂ)*_=(t : ℂ)^w*((1+t^2 : ℝ) : ℂ)^(-((w+2)/2))
  rw [← hp]
  calc
    _ = cauchyWeight w t⁻¹*((t : ℂ)^w*(t : ℂ)^(-(w+2))) := by
      rw [← Complex.cpow_add _ _ hn,show w+ -(w+2)=(-2 : ℂ) by ring,mul_comm]
    _ = _ := by unfold cauchyWeight; ring

private theorem weight_mellin_convergent {w : ℂ} (hw : 2 < w.re) :
    MellinConvergent (cauchyWeight w) 1 := by
  simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul] using
    (cauchyWeight_integrable hw).integrableOn (s := Ioi 0)

/-- The spectral moment is absolutely integrable, by inversion of the positive half-line. -/
theorem spectralWeight_integrable {w : ℂ} (hw : 2 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^w*cauchyWeight w t) (Ioi 0) := by
  have hi := (MellinConvergent.comp_rpow (f := cauchyWeight w) (s := -1)
    (a := -1) (by norm_num)).mpr (by simpa using weight_mellin_convergent hw)
  have hi' : IntegrableOn (fun t : ℝ => (t : ℂ)^(-2 : ℂ)*cauchyWeight w t⁻¹) (Ioi 0) := by
    simpa only [MellinConvergent,Real.rpow_neg_one,smul_eq_mul,
      show (-1 : ℂ)-1= -2 by ring] using! hi
  exact MeasureTheory.IntegrableOn.congr_fun hi'
    (fun t ht => reciprocal_weight ht w) measurableSet_Ioi

/-- Both axes have the same Cauchy normalization. -/
theorem spectralWeight_integral {w : ℂ} (hw : 2 < w.re) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^w*cauchyWeight w t)=averagingFactor w := by
  have h := mellin_comp_inv (cauchyWeight w) (-1)
  simp only [neg_neg,mellin,sub_self,Complex.cpow_zero,one_mul,
    smul_eq_mul,show (-1 : ℂ)-1= -2 by ring] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => reciprocal_weight ht w),
    cauchyWeight_integral hw] at h
  exact h

private theorem kernel_over_t {t : ℝ} (ht : 0 < t) (w : ℂ) :
    cauchyKernel w t/(t : ℂ)=(averagingFactor w)⁻¹*cauchyWeight w t := by
  unfold cauchyKernel
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

/-- The zeroth Mellin moment of the normalized kernel equals one. -/
theorem cauchyKernel_mellin_zero {w : ℂ} (hw : 2 < w.re) :
    HasMellin (cauchyKernel w) 0 1 := by
  have hi : IntegrableOn (fun t : ℝ => (t : ℂ)⁻¹*cauchyKernel w t) (Ioi 0) := by
    have h := ((cauchyWeight_integrable hw).integrableOn (s := Ioi (0 : ℝ))).const_mul (averagingFactor w)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro t ht
    simpa only [div_eq_mul_inv,mul_comm] using (kernel_over_t ht w).symm
  constructor
  · simpa only [MellinConvergent,zero_sub,Complex.cpow_neg_one,smul_eq_mul] using hi
  · rw [mellin]
    simp only [zero_sub,Complex.cpow_neg_one,smul_eq_mul]
    calc
      _ = ∫ t in Ioi (0 : ℝ), (averagingFactor w)⁻¹*cauchyWeight w t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa only [div_eq_mul_inv,mul_comm] using kernel_over_t ht w
      _ = 1 := by rw [integral_const_mul,cauchyWeight_integral hw,
        inv_mul_cancel₀ (averagingFactor_ne_zero hw)]

private theorem spectral_kernel {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ)^(w-1)*cauchyKernel w t=
      (averagingFactor w)⁻¹*((t : ℂ)^w*cauchyWeight w t) := by
  have hn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [cauchyKernel]
  calc
    _ = (averagingFactor w)⁻¹*(((t : ℂ)^(w-1)*(t : ℂ)^(1 : ℂ))*cauchyWeight w t) := by
      rw [Complex.cpow_one]; ring
    _ = _ := by rw [← Complex.cpow_add _ _ hn,sub_add_cancel]

/-- The spectral Mellin moment also equals one, so the power axis is preserved. -/
theorem cauchyKernel_mellin_spectral {w : ℂ} (hw : 2 < w.re) :
    HasMellin (cauchyKernel w) w 1 := by
  constructor
  · have hi := (spectralWeight_integrable hw).const_mul (averagingFactor w)⁻¹
    change IntegrableOn (fun t : ℝ => (t : ℂ)^(w-1) • cauchyKernel w t) (Ioi 0)
    simp only [smul_eq_mul]
    exact MeasureTheory.IntegrableOn.congr_fun hi
      (fun t ht => (spectral_kernel ht w).symm) measurableSet_Ioi
  · rw [mellin]
    simp only [smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => spectral_kernel ht w),
      integral_const_mul,spectralWeight_integral hw,inv_mul_cancel₀ (averagingFactor_ne_zero hw)]

#print axioms cauchyWeight_integrable
#print axioms cauchyWeight_integral
#print axioms spectralWeight_integrable
#print axioms spectralWeight_integral
#print axioms cauchyKernel_mellin_zero
#print axioms cauchyKernel_mellin_spectral
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyMoments
