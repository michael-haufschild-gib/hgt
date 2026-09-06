import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleBoundaryBounds

/-!
# One-sided primitives for the actual Gamma pole boundary masses

The ordinary endpoint logarithm is integrable by the admitted screw-tail half
moment. Translation identifies the actual cross mass with its single primitive
and the weighted self mass with two exponential primitives. Their lower endpoint
is fixed, so local aperture differentiation never differentiates at the singular
endpoint. No positivity of the Weil source or RH premise is used.
-/

open MeasureTheory Set
noncomputable section
namespace RHTower

/-- The ordinary positive-endpoint logarithm whose primitive gives the cross boundary mass. -/
def ccmGammaPoleBoundaryLog (t : ℝ) : ℝ := -Real.log (1-Real.exp (-t))

private theorem log_nonneg {t : ℝ} (ht : 0<t) : 0≤ccmGammaPoleBoundaryLog t := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos
  · exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  · linarith [Real.exp_pos (-t)]

/-- Integrability of the doubled boundary logarithm at its singular endpoint. -/
theorem intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul {T : ℝ} (hT : 0<T) :
    IntervalIntegrable (fun t => ccmGammaPoleBoundaryLog (2*t)) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
  have hi : IntegrableOn (fun t => 2*(screwTailPrimitive t*Real.exp (-(t/2)))) (Ioc 0 T) volume :=
    (integrableOn_screwTailPrimitive_mul_exp_half.mono_set (fun _ hx => hx.1)).const_mul 2
  apply hi.mono'
    ((by unfold ccmGammaPoleBoundaryLog; fun_prop :
      Measurable (fun t : ℝ => ccmGammaPoleBoundaryLog (2*t))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (log_nonneg (by linarith [ht.1] : 0<2*t))]
  exact ccmGammaBoundaryLog_le_screwHalfMoment ht.1

/-- Integrability across the logarithmic endpoint, obtained from the admitted screw half moment. -/
theorem intervalIntegrable_ccmGammaPoleBoundaryLog {T : ℝ} (hT : 0<T) :
    IntervalIntegrable ccmGammaPoleBoundaryLog volume 0 T := by
  have hi := (intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (show 0<T/2 by linarith)).comp_mul_left (c := 1/2)
  convert! hi using 1
  · ext t
    congr 1
    ring
  · ring
  · ring

private theorem pullback_integrable (a : SuzukiPositiveAperture) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (2*a.1)) :
    IntegrableOn (fun x => f (a.1-x)) (centralInterval a.1) volume ∧
    IntegrableOn (fun x => f (a.1+x)) (centralInterval a.1) volume := by
  have hm := (hf.comp_sub_left a.1).symm
  have hp := hf.comp_add_left a.1
  rw [sub_zero,show a.1-2*a.1= -a.1 by ring] at hm
  rw [zero_sub,show 2*a.1-a.1=a.1 by ring] at hp
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [a.2])).mp hm,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [a.2])).mp hp⟩

private theorem pullback_sub (a : SuzukiPositiveAperture) (f : ℝ → ℝ) :
    (∫ x in centralInterval a.1, f (a.1-x)) = ∫ t in 0..2*a.1, f t := by
  rw [centralInterval,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.2]),
    intervalIntegral.integral_comp_sub_left,sub_self,show a.1-(-a.1)=2*a.1 by ring]

private theorem pullback_add (a : SuzukiPositiveAperture) (f : ℝ → ℝ) :
    (∫ x in centralInterval a.1, f (a.1+x)) = ∫ t in 0..2*a.1, f t := by
  rw [centralInterval,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show -a.1≤a.1 by linarith [a.2]),
    intervalIntegral.integral_comp_add_left,add_neg_cancel,show a.1+a.1=2*a.1 by ring]

private theorem boundary_eq (R L : ℝ) :
    ccmGammaPolarBoundary R L = (1/2)*ccmGammaPoleBoundaryLog (2*R)+
      (ccmGammaPoleBoundaryLog L-(1/2)*ccmGammaPoleBoundaryLog (2*L)) := by
  unfold ccmGammaPolarBoundary ccmGammaPoleBoundaryLog
  ring

/-- Fixed-lower-endpoint primitive for the actual unweighted Gamma boundary mass. -/
def ccmGammaPoleCrossBoundaryPrimitive (s : ℝ) : ℝ :=
  ∫ t in 0..2*s, ccmGammaPoleBoundaryLog t

/-- The two translated logarithmic tails cancel exactly in the cross boundary mass. -/
theorem ccmGammaPoleCrossBoundaryMass_eq_primitive (a : SuzukiPositiveAperture) :
    ccmGammaPoleCrossBoundaryMass a=ccmGammaPoleCrossBoundaryPrimitive a.1 := by
  have h1 := pullback_integrable a ccmGammaPoleBoundaryLog
    (intervalIntegrable_ccmGammaPoleBoundaryLog (by linarith [a.2]))
  have h2 := pullback_integrable a (fun t => ccmGammaPoleBoundaryLog (2*t))
    (intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (by linarith [a.2]))
  unfold ccmGammaPoleCrossBoundaryMass ccmGammaPoleCrossBoundaryPrimitive
  simp_rw [boundary_eq]
  have hsum := integral_add (h2.1.const_mul (1/2)) (h1.2.sub (h2.2.const_mul (1/2)))
  simp only [Pi.sub_apply] at hsum
  rw [hsum,
    integral_sub h1.2 (h2.2.const_mul (1/2)),integral_const_mul,integral_const_mul,
    pullback_sub a (fun t => ccmGammaPoleBoundaryLog (2*t)),pullback_add a ccmGammaPoleBoundaryLog,
    pullback_add a (fun t => ccmGammaPoleBoundaryLog (2*t))]
  ring

private theorem weighted_pullback_sub (a : SuzukiPositiveAperture) (f : ℝ → ℝ) :
    (∫ x in centralInterval a.1, Real.exp x*f (a.1-x)) =
      Real.exp a.1 * ∫ t in 0..2*a.1, Real.exp (-t)*f t := by
  have he (x : ℝ) : Real.exp x*f (a.1-x)=
      Real.exp a.1*(Real.exp (-(a.1-x))*f (a.1-x)) := by
    rw [← mul_assoc,← Real.exp_add,show a.1+(-(a.1-x))=x by ring]
  simp_rw [he]
  rw [integral_const_mul,pullback_sub a (fun t => Real.exp (-t)*f t)]

private theorem weighted_pullback_add (a : SuzukiPositiveAperture) (f : ℝ → ℝ) :
    (∫ x in centralInterval a.1, Real.exp x*f (a.1+x)) =
      Real.exp (-a.1) * ∫ t in 0..2*a.1, Real.exp t*f t := by
  have he (x : ℝ) : Real.exp x*f (a.1+x)=
      Real.exp (-a.1)*(Real.exp (a.1+x)*f (a.1+x)) := by
    rw [← mul_assoc,← Real.exp_add,show -a.1+(a.1+x)=x by ring]
  simp_rw [he]
  rw [integral_const_mul,pullback_add a (fun t => Real.exp t*f t)]

/-- Fixed-lower-endpoint representation of the exponentially weighted Gamma boundary mass. -/
def ccmGammaPoleSelfBoundaryPrimitive (s : ℝ) : ℝ :=
  Real.exp s/2 * (∫ t in 0..2*s, Real.exp (-t)*ccmGammaPoleBoundaryLog (2*t)) +
    Real.exp (-s) * ∫ t in 0..2*s,
      Real.exp t*(ccmGammaPoleBoundaryLog t-ccmGammaPoleBoundaryLog (2*t)/2)

/-- The actual weighted boundary mass is the exact sum of two one-sided primitives. -/
theorem ccmGammaPoleSelfBoundaryMass_eq_primitive (a : SuzukiPositiveAperture) :
    ccmGammaPoleSelfBoundaryMass a=ccmGammaPoleSelfBoundaryPrimitive a.1 := by
  have h1 := pullback_integrable a ccmGammaPoleBoundaryLog
    (intervalIntegrable_ccmGammaPoleBoundaryLog (by linarith [a.2]))
  have h2 := pullback_integrable a (fun t => ccmGammaPoleBoundaryLog (2*t))
    (intervalIntegrable_ccmGammaPoleBoundaryLog_two_mul (by linarith [a.2]))
  have he : ContinuousOn Real.exp (centralInterval a.1) := Real.continuous_exp.continuousOn
  have hw1 := h2.1.continuousOn_mul he (isCompact_Icc)
  have hw2 := (h1.2.sub (h2.2.const_mul (1/2))).continuousOn_mul he (isCompact_Icc)
  unfold ccmGammaPoleSelfBoundaryMass ccmGammaPoleSelfBoundaryPrimitive
  have hp (x : ℝ) : Real.exp x*ccmGammaPolarBoundary (a.1-x) (a.1+x)=
      (1/2)*(Real.exp x*ccmGammaPoleBoundaryLog (2*(a.1-x)))+
      Real.exp x*(ccmGammaPoleBoundaryLog (a.1+x)-(1/2)*ccmGammaPoleBoundaryLog (2*(a.1+x))) := by
    rw [boundary_eq]
    ring
  simp_rw [hp]
  have hsum := integral_add (hw1.const_mul (1/2)) hw2
  simp only [Pi.sub_apply] at hsum
  rw [hsum,integral_const_mul,
    weighted_pullback_sub a (fun t => ccmGammaPoleBoundaryLog (2*t)),
    weighted_pullback_add a (fun t => ccmGammaPoleBoundaryLog t-(1/2)*ccmGammaPoleBoundaryLog (2*t))]
  simp only [div_eq_mul_inv]
  congr 1
  · ring
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    ring

end RHTower
