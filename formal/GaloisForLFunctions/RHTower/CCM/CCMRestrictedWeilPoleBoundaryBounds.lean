import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleIntegratedPrimeError
import GaloisForLFunctions.RHTower.ScrewTailHalfMoment
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Uniform bounds for the actual Weil pole boundary masses

The convex scalar inequality `x log x ≥ x - 1` bounds the endpoint logarithm
by the corpus's integrable screw-tail half moment. Its exact half-line mass
then bounds both actual aperture boundary masses, uniformly in every positive
aperture. No numerical estimate of the logarithmic integral is used.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- The positive screw-tail half moment dominates the Gamma endpoint logarithm. -/
theorem ccmGammaBoundaryLog_le_screwHalfMoment {t : ℝ} (ht : 0<t) :
    -Real.log (1-Real.exp (-(2*t))) ≤
      2*(screwTailPrimitive t*Real.exp (-(t/2))) := by
  let u := Real.exp (-(t/2))
  have hu : 0<u := Real.exp_pos _
  have hu1 : u<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.self_sub_one_le_mul_log (by linarith : 0≤1+u)
  have hm := Real.self_sub_one_le_mul_log (by linarith : 0≤1-u)
  have he : Real.exp (-t)=u*u := by
    dsimp [u]
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : 1-Real.exp (-t)=(1-u)*(1+u) := by rw [he];ring
  have hlog : Real.log (1-Real.exp (-t))=Real.log (1-u)+Real.log (1+u) := by
    rw [hf,Real.log_mul (by linarith : 1-u≠0) (by linarith : 1+u≠0)]
  have hmono : -Real.log (1-Real.exp (-(2*t)))≤-Real.log (1-Real.exp (-t)) := by
    apply neg_le_neg
    apply Real.log_le_log (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
    have hh := Real.exp_le_exp.mpr (show -(2*t)≤-t by linarith)
    linarith
  have harc : 0≤Real.arctan u := Real.arctan_nonneg.mpr hu.le
  rw [hlog] at hmono
  change _≤2*(((Real.log (1+u)-Real.log (1-u))/2+Real.arctan u)*u)
  nlinarith

/-- Each actual boundary value is controlled by two translated integrable
screw-tail half moments and one exponential tail. -/
theorem ccmGammaPolarBoundary_le_halfMoment_tails {R L : ℝ} (hR : 0<R) (hL : 0<L) :
    ccmGammaPolarBoundary R L ≤
      screwTailPrimitive R*Real.exp (-(R/2))+
      screwTailPrimitive L*Real.exp (-(L/2))+Real.exp (-L) := by
  have hRlog := ccmGammaBoundaryLog_le_screwHalfMoment hR
  have hLlog := ccmGammaBoundaryLog_le_screwHalfMoment hL
  have hp := Real.log_le_sub_one_of_pos (show 0<1+Real.exp (-L) by positivity)
  rw [ccmGammaPolarBoundary_symmetric_decomposition hL]
  linarith

private theorem interval_integrable_halfMoment (a : SuzukiPositiveAperture) :
    IntervalIntegrable (fun t => screwTailPrimitive t*Real.exp (-(t/2))) volume 0 (2*a.1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [a.property])).mpr
  exact integrableOn_screwTailPrimitive_mul_exp_half.mono_set (fun _ hx => hx.1)

private theorem aperture_pullback_integrable (a : SuzukiPositiveAperture) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (2*a.1)) :
    IntegrableOn (fun x => f (a.1-x)) (centralInterval a.1) volume ∧
    IntegrableOn (fun x => f (a.1+x)) (centralInterval a.1) volume := by
  have hm := (hf.comp_sub_left a.1).symm
  have hp := hf.comp_add_left a.1
  rw [sub_zero, show a.1-2*a.1 = -a.1 by ring] at hm
  rw [zero_sub, show 2*a.1-a.1=a.1 by ring] at hp
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [a.property])).mp hm,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [a.property])).mp hp⟩

private theorem aperture_pullback_integral (a : SuzukiPositiveAperture) (f : ℝ → ℝ) :
    (∫ x in centralInterval a.1, f (a.1-x)) = ∫ t in 0..2*a.1, f t := by
  rw [centralInterval,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.property]),
    intervalIntegral.integral_comp_sub_left]
  rw [sub_self,show a.1-(-a.1)=2*a.1 by ring]

private theorem aperture_pullback_integral_add (a : SuzukiPositiveAperture) (f : ℝ → ℝ) :
    (∫ x in centralInterval a.1, f (a.1+x)) = ∫ t in 0..2*a.1, f t := by
  rw [centralInterval,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.property]),
    intervalIntegral.integral_comp_add_left]
  rw [add_neg_cancel,show a.1+a.1=2*a.1 by ring]

private theorem integral_halfMoment_le (a : SuzukiPositiveAperture) :
    (∫ t in 0..2*a.1, screwTailPrimitive t*Real.exp (-(t/2))) ≤ Real.log 2+Real.pi/2 := by
  rw [intervalIntegral.integral_of_le (show 0≤2*a.1 by linarith [a.property])]
  rw [← integral_Ioi_screwTailPrimitive_mul_exp_half]
  refine setIntegral_mono_set integrableOn_screwTailPrimitive_mul_exp_half ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact screwTailPrimitive_mul_exp_half_nonneg ht
  · exact Filter.Eventually.of_forall fun _ hx => hx.1

/-- The exact unweighted Gamma boundary mass has a uniform aperture-independent bound. -/
theorem ccmGammaPoleCrossBoundaryMass_le (a : SuzukiPositiveAperture) :
    ccmGammaPoleCrossBoundaryMass a ≤ 2*Real.log 2+Real.pi+1 := by
  let f : ℝ → ℝ := fun t => screwTailPrimitive t*Real.exp (-(t/2))
  have hfi := aperture_pullback_integrable a f (interval_integrable_halfMoment a)
  have hec : Continuous (fun x : ℝ => Real.exp (-(a.1+x))) := by fun_prop
  have hei := hec.integrableOn_Icc (a:= -a.1) (b:=a.1) (μ:=volume)
  have hB : IntegrableOn (fun x => ccmGammaPolarBoundary (a.1-x) (a.1+x))
      (centralInterval a.1) volume := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using integrableOn_ccmGammaPolarBoundary_exp_weight a 0
  have hmono : (∫ x in centralInterval a.1, ccmGammaPolarBoundary (a.1-x) (a.1+x)) ≤
      ∫ x in centralInterval a.1, (f (a.1-x)+f (a.1+x))+Real.exp (-(a.1+x)) := by
    apply integral_mono_ae hB ((hfi.1.add hfi.2).add hei)
    rw [centralInterval,Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ccmGammaPolarBoundary_le_halfMoment_tails (by linarith [hx.2]) (by linarith [hx.1])
  have hs := integral_add (hfi.1.add hfi.2) hei
  simp only [Pi.add_apply] at hs
  rw [hs,integral_add hfi.1 hfi.2,aperture_pullback_integral,aperture_pullback_integral_add,
    aperture_pullback_integral_add a (fun t => Real.exp (-t))] at hmono
  have he : (∫ t in 0..2*a.1, Real.exp (-t))≤1 := by
    rw [intervalIntegral.integral_comp_neg,integral_exp]
    simp only [neg_zero,Real.exp_zero]
    linarith [Real.exp_pos (-(2*a.1))]
  have hf := integral_halfMoment_le a
  change (∫ t in 0..2*a.1, f t)≤Real.log 2+Real.pi/2 at hf
  change ccmGammaPoleCrossBoundaryMass a ≤ _ at hmono
  linarith

/-- The weighted boundary mass costs at most the physical endpoint exponential
 times the unweighted mass. -/
theorem ccmGammaPoleSelfBoundaryMass_le_scaled_cross (a : SuzukiPositiveAperture) :
    ccmGammaPoleSelfBoundaryMass a ≤ Real.exp a.1*ccmGammaPoleCrossBoundaryMass a := by
  have hB : IntegrableOn (fun x => ccmGammaPolarBoundary (a.1-x) (a.1+x))
      (centralInterval a.1) volume := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using integrableOn_ccmGammaPolarBoundary_exp_weight a 0
  have hB1 : IntegrableOn (fun x => Real.exp x*ccmGammaPolarBoundary (a.1-x) (a.1+x))
      (centralInterval a.1) volume := by
    simpa only [one_mul] using integrableOn_ccmGammaPolarBoundary_exp_weight a 1
  change (∫ x in centralInterval a.1, Real.exp x*ccmGammaPolarBoundary (a.1-x) (a.1+x)) ≤ _
  rw [ccmGammaPoleCrossBoundaryMass,← integral_const_mul]
  apply integral_mono_ae hB1 (hB.const_mul (Real.exp a.1))
  rw [centralInterval,Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx.2.le)
    (ccmGammaPolarBoundary_pos (by linarith [hx.2]) (by linarith [hx.1])).le

/-- The actual weighted Gamma boundary mass has its uniform exponential bound. -/
theorem ccmGammaPoleSelfBoundaryMass_le (a : SuzukiPositiveAperture) :
    ccmGammaPoleSelfBoundaryMass a ≤ (2*Real.log 2+Real.pi+1)*Real.exp a.1 := by
  calc
    _ ≤ Real.exp a.1*ccmGammaPoleCrossBoundaryMass a := ccmGammaPoleSelfBoundaryMass_le_scaled_cross a
    _ ≤ Real.exp a.1*(2*Real.log 2+Real.pi+1) :=
      mul_le_mul_of_nonneg_left (ccmGammaPoleCrossBoundaryMass_le a) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end RHTower
