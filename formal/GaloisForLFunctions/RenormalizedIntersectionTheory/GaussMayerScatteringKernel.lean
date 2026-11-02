import GaloisForLFunctions.HTGeometry.BarnesConeKernelAnalytic

/-! The Mellin kernel of the zeta-cleared primitive-cone response is even.
Its only singular term is `2/(a*t²)`. A fixed analytic cylinder remainder
expresses the regular part for complex periods with positive real part. -/

open Complex Set Filter Metric Topology
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringKernel

/-- The centered cylinder kernel, equal to `(z/2)coth(z/2)` off its poles. -/
def evenCylinder (z : ℂ) : ℂ := cylKernelFactor 1 z-z/2

private theorem analyticAt_evenCylinder_zero : AnalyticAt ℂ evenCylinder 0 :=
  (analyticAt_cylKernelFactor one_ne_zero).sub
    (analyticAt_id.div analyticAt_const (by norm_num))

private theorem evenCylinder_zero : evenCylinder 0=1 := by simp [evenCylinder]

private theorem cylinder_reflection_algebra (z E : ℂ) (hE : E ≠ 0) (h1 : 1-E ≠ 0) :
    z/(1-E)-(-z)/(1-E⁻¹)=z := by
  have hi : 1-E⁻¹ ≠ 0 := by
    intro he
    apply h1
    have hE1 : E=1 := inv_eq_one.mp (sub_eq_zero.mp he).symm
    rw [hE1,sub_self]
  have hE1 : E-1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h1))
  have hE1' : -1+E ≠ 0 := by simpa only [sub_eq_add_neg,add_comm] using hE1
  field_simp [hE,h1,hi,hE1,hE1']
  ring

private theorem evenCylinder_neg_of_small {z : ℂ} (hz : ‖z‖ < 2*Real.pi) :
    evenCylinder (-z)=evenCylinder z := by
  by_cases hz0 : z=0
  · rw [hz0,neg_zero]
  · have hden : 1-Complex.exp (-z) ≠ 0 := by
      simpa only [one_mul] using
        one_sub_exp_neg_mul_ne_zero (o := (1 : ℂ)) one_ne_zero hz0 (by simpa using hz)
    have h := cylinder_reflection_algebra z (Complex.exp (-z)) (Complex.exp_ne_zero _) hden
    have he : Complex.exp z=(Complex.exp (-z))⁻¹ := by rw [Complex.exp_neg,inv_inv]
    rw [evenCylinder,evenCylinder,cylKernelFactor_of_ne hz0,
      cylKernelFactor_of_ne (neg_ne_zero.mpr hz0)]
    simp only [one_mul,neg_neg]
    rw [he]
    linear_combination -h

/-- Centering removes the odd part, so the linear Taylor coefficient vanishes. -/
theorem deriv_evenCylinder_zero : deriv evenCylinder 0=0 := by
  have hd := analyticAt_evenCylinder_zero.differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun z => evenCylinder (-z)) (-deriv evenCylinder 0) 0 := by
    simpa only [Function.comp_def,neg_smul,one_smul] using
      hd.scomp_of_eq (h := fun z : ℂ => -z) 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)
  have he : (fun z => evenCylinder (-z)) =ᶠ[𝓝 (0 : ℂ)] evenCylinder := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (show 0 < 2*Real.pi by positivity)] with z hz
    apply evenCylinder_neg_of_small
    simpa only [mem_ball,dist_zero_right] using hz
  have h := (hn.congr_of_eventuallyEq he.symm).unique hd
  linear_combination -(1/2 : ℂ)*h

/-- Fixed analytic second remainder of the centered cylinder. -/
def cylinderRemainder : ℂ → ℂ := analyticSlope (analyticSlope evenCylinder 0) 0

/-- Exact expansion, including the value at the removable singularity. -/
theorem evenCylinder_expansion (z : ℂ) :
    evenCylinder z=1+z^2*cylinderRemainder z := by
  have h := eq_taylor_two_add_sq_mul evenCylinder 0 z
  simpa only [evenCylinder_zero,deriv_evenCylinder_zero,sub_zero,mul_zero,add_zero,
    cylinderRemainder] using h

/-- The fixed cylinder remainder is analytic across zero. -/
theorem analyticAt_cylinderRemainder_zero : AnalyticAt ℂ cylinderRemainder 0 :=
  analyticAt_analyticSlope_two analyticAt_evenCylinder_zero

private theorem cylinderRemainder_eq {z : ℂ} (hz : z ≠ 0) :
    cylinderRemainder z=(evenCylinder z-1)/z^2 := by
  rw [eq_div_iff (pow_ne_zero 2 hz)]
  linear_combination -(evenCylinder_expansion z)

/-- Positive real part keeps the exponential denominator away from zero. -/
theorem exponential_denominator_ne_zero {z : ℂ} (hz : 0 < z.re) :
    1-Complex.exp (-z) ≠ 0 := by
  have hn : ‖Complex.exp (-z)‖ < 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr (by simpa only [Complex.neg_re] using neg_neg_of_pos hz)
  intro he
  rw [(sub_eq_zero.mp he).symm,norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

private theorem analyticAt_evenCylinder {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ evenCylinder z := by
  have hz0 : z ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at hz
  have he : evenCylinder =ᶠ[𝓝 z]
      fun t => t/(1-Complex.exp (-t))-t/2 := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with t ht
    rw [evenCylinder,cylKernelFactor_of_ne ht,one_mul]
  rw [analyticAt_congr he]
  exact (analyticAt_id.div (analyticAt_const.sub analyticAt_id.neg.cexp')
    (exponential_denominator_ne_zero hz)).sub
      (analyticAt_id.div analyticAt_const (by norm_num))

/-- The same fixed remainder is analytic on the entire open right half-plane. -/
theorem analyticAt_cylinderRemainder {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ cylinderRemainder z := by
  have hz0 : z ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at hz
  have he : cylinderRemainder =ᶠ[𝓝 z] fun t => (evenCylinder t-1)/t^2 := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with t ht
    exact cylinderRemainder_eq ht
  rw [analyticAt_congr he]
  exact ((analyticAt_evenCylinder hz).sub analyticAt_const).div (analyticAt_id.pow 2)
    (pow_ne_zero 2 hz0)

/-- Mellin kernel of the two boundary rays and doubled positive lattice cone. -/
def kernel (a t : ℂ) : ℂ :=
  (Complex.exp (-t)+Complex.exp (-(a*t)))/
    ((1-Complex.exp (-t))*(1-Complex.exp (-(a*t))))

/-- Regular part expressed using a single fixed analytic function. -/
def regularKernel (a t : ℂ) : ℂ :=
  2/a*cylinderRemainder t+2*a*cylinderRemainder (a*t)+
    2*a*t^2*cylinderRemainder t*cylinderRemainder (a*t)-1/2

private theorem kernel_eq_centered {a t : ℂ} (ha : a ≠ 0) (ht : t ≠ 0)
    (h1 : 1-Complex.exp (-t) ≠ 0) (h2 : 1-Complex.exp (-(a*t)) ≠ 0) :
    kernel a t=2/(a*t^2)*evenCylinder t*evenCylinder (a*t)-1/2 := by
  rw [kernel,evenCylinder,evenCylinder,cylKernelFactor_of_ne ht,
    cylKernelFactor_of_ne (mul_ne_zero ha ht)]
  simp only [one_mul]
  have h2' : 1-Complex.exp (-(t*a)) ≠ 0 := by simpa only [mul_comm] using h2
  field_simp [ha,ht,h1,h2,h2']
  ring

/-- The complex-period kernel has only its double singular term; the simple term cancels. -/
theorem kernel_decomposition {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    kernel a (t : ℂ)=2/(a*(t : ℂ)^2)+regularKernel a (t : ℂ) := by
  have ha0 : a ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at ha
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hat : 0 < (a*(t : ℂ)).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using mul_pos ha ht
  rw [kernel_eq_centered ha0 ht0 (exponential_denominator_ne_zero ht)
    (exponential_denominator_ne_zero hat),evenCylinder_expansion,evenCylinder_expansion,
    regularKernel]
  field_simp [ha0,ht0]
  ring

/-- For a nonnegative real Mellin coordinate, the regular kernel is holomorphic in its period. -/
theorem analyticAt_regularKernel_period {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℂ (fun b => regularKernel b (t : ℂ)) a := by
  have ha0 : a ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at ha
  have hU : AnalyticAt ℂ cylinderRemainder (a*(t : ℂ)) := by
    rcases eq_or_lt_of_le ht with rfl | htpos
    · simpa only [Complex.ofReal_zero,mul_zero] using analyticAt_cylinderRemainder_zero
    · apply analyticAt_cylinderRemainder
      simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        using mul_pos ha htpos
  have hUc := hU.comp (f := fun b : ℂ => b*(t : ℂ)) (analyticAt_id.mul analyticAt_const)
  exact (((analyticAt_const.div analyticAt_id ha0).mul analyticAt_const).add
    ((analyticAt_const.mul analyticAt_id).mul hUc)).add
      ((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul analyticAt_const).mul hUc)
    |>.sub analyticAt_const

private theorem analyticAt_cylinderRemainder_mul_real {a : ℂ} (ha : 0 < a.re)
    {t : ℝ} (ht : 0 ≤ t) : AnalyticAt ℂ cylinderRemainder (a*(t : ℂ)) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simpa only [Complex.ofReal_zero,mul_zero] using analyticAt_cylinderRemainder_zero
  · apply analyticAt_cylinderRemainder
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      using mul_pos ha htpos

/-- The regular kernel varies continuously jointly in complex period and real Mellin coordinate. -/
theorem continuousAt_regularKernel {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun p : ℂ × ℝ => regularKernel p.1 (p.2 : ℂ)) (a,t) := by
  have ha0 : a ≠ 0 := by intro he; simp only [he,Complex.zero_re,lt_self_iff_false] at ha
  have htime : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hUt : ContinuousAt (fun p : ℂ × ℝ => cylinderRemainder (p.2 : ℂ)) (a,t) := by
    have h := (analyticAt_cylinderRemainder_mul_real (a := 1) (by norm_num) ht).continuousAt
    simp only [one_mul] at h
    exact h.comp (f := fun p : ℂ × ℝ => (p.2 : ℂ)) (x := (a,t)) htime.continuousAt
  have hUat : ContinuousAt (fun p : ℂ × ℝ => cylinderRemainder (p.1*(p.2 : ℂ))) (a,t) :=
    (analyticAt_cylinderRemainder_mul_real ha ht).continuousAt.comp
      (f := fun p : ℂ × ℝ => p.1*(p.2 : ℂ)) (x := (a,t))
      (continuous_fst.mul htime).continuousAt
  exact ((((continuousAt_const.div continuous_fst.continuousAt ha0).mul hUt).add
    ((continuousAt_const.mul continuous_fst.continuousAt).mul hUat)).add
      ((((continuousAt_const.mul continuous_fst.continuousAt).mul
        (htime.continuousAt.pow 2)).mul hUt).mul hUat)).sub continuousAt_const

private theorem period_re_lower {a : ℂ} (ha : a ∈ closedBall (2 : ℂ) (3/2 : ℝ)) :
    (1/2 : ℝ) ≤ a.re := by
  have hr := (neg_le_abs (a-2).re).trans (Complex.abs_re_le_norm (a-2))
  have hd : ‖a-2‖ ≤ (3/2 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using ha
  norm_num [Complex.sub_re] at hr
  linarith only [hr,hd]

private theorem period_re_pos {a : ℂ} (ha : a ∈ closedBall (2 : ℂ) (3/2 : ℝ)) :
    0 < a.re := lt_of_lt_of_le (by norm_num) (period_re_lower ha)

/-- The entire closed Mayer period disc has one uniform bound for the subtracted head kernel. -/
theorem regularKernel_uniform_bound :
    ∃ C : ℝ, ∀ a ∈ closedBall (2 : ℂ) (3/2 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖regularKernel a (t : ℂ)‖ ≤ C := by
  have hc : IsCompact (closedBall (2 : ℂ) (3/2 : ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall (2 : ℂ) (3/2 : ℝ)).prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℂ × ℝ => regularKernel p.1 (p.2 : ℂ))
      (closedBall (2 : ℂ) (3/2 : ℝ) ×ˢ Icc (0 : ℝ) 1) :=
    fun p hp => (continuousAt_regularKernel (period_re_pos hp.1) hp.2.1).continuousWithinAt
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hcont
  exact ⟨C,fun a ha t ht => hC (a,t) ⟨ha,ht⟩⟩

/-- The unsubtracted kernel is holomorphic in every positive-real-part complex period. -/
theorem analyticAt_kernel_period {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℂ (fun b => kernel b (t : ℂ)) a := by
  have hat : 0 < (a*(t : ℂ)).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      using mul_pos ha ht
  have hE : AnalyticAt ℂ (fun b : ℂ => Complex.exp (-(b*(t : ℂ)))) a :=
    (analyticAt_id.mul analyticAt_const).neg.cexp'
  exact (analyticAt_const.add hE).div
    (analyticAt_const.mul (analyticAt_const.sub hE))
    (mul_ne_zero (exponential_denominator_ne_zero ht) (exponential_denominator_ne_zero hat))

/-- Joint continuity supplies the actual disc-valued kernel away from the Mellin endpoint. -/
theorem continuousAt_kernel {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun p : ℂ × ℝ => kernel p.1 (p.2 : ℂ)) (a,t) := by
  have hat : 0 < (a*(t : ℂ)).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      using mul_pos ha ht
  have hN : Continuous (fun p : ℂ × ℝ =>
      Complex.exp (-(p.2 : ℂ))+Complex.exp (-(p.1*(p.2 : ℂ)))) := by fun_prop
  have hD : Continuous (fun p : ℂ × ℝ =>
      (1-Complex.exp (-(p.2 : ℂ)))*(1-Complex.exp (-(p.1*(p.2 : ℂ))))) := by fun_prop
  exact hN.continuousAt.div hD.continuousAt
    (mul_ne_zero (exponential_denominator_ne_zero ht) (exponential_denominator_ne_zero hat))

/-- The entire closed Mayer period disc has one exponentially decaying tail majorant. -/
theorem kernel_uniform_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ closedBall (2 : ℂ) (3/2 : ℝ), ∀ t : ℝ, 1 ≤ t →
      ‖kernel a (t : ℂ)‖ ≤ C*Real.exp (-t/2) := by
  let d : ℝ := 1-Real.exp (-(1/2 : ℝ))
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  refine ⟨2/d^2,div_pos (by norm_num) (sq_pos_of_pos hd),?_⟩
  intro a ha t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hRe := period_re_lower ha
  have hprod := mul_le_mul_of_nonneg_right hRe ht0.le
  have hE : ‖Complex.exp (-(t : ℂ))‖ ≤ Real.exp (-t/2) := by
    rw [Complex.norm_exp,Complex.neg_re,Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    linarith only [ht0]
  have hF : ‖Complex.exp (-(a*(t : ℂ)))‖ ≤ Real.exp (-t/2) := by
    rw [Complex.norm_exp,Complex.neg_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    apply Real.exp_le_exp.mpr
    linarith only [hprod]
  have hexp : Real.exp (-t/2) ≤ Real.exp (-(1/2 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith only [ht])
  have hD1 : d ≤ ‖1-Complex.exp (-(t : ℂ))‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.exp (-(t : ℂ)))
    rw [norm_one] at h
    dsimp [d]
    linarith only [h,hE,hexp]
  have hD2 : d ≤ ‖1-Complex.exp (-(a*(t : ℂ)))‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.exp (-(a*(t : ℂ))))
    rw [norm_one] at h
    dsimp [d]
    linarith only [h,hF,hexp]
  have hD : d^2 ≤ ‖1-Complex.exp (-(t : ℂ))‖*‖1-Complex.exp (-(a*(t : ℂ)))‖ := by
    simpa only [pow_two] using mul_le_mul hD1 hD2 hd.le (norm_nonneg _)
  have hN : ‖Complex.exp (-(t : ℂ))+Complex.exp (-(a*(t : ℂ)))‖ ≤ 2*Real.exp (-t/2) :=
    (norm_add_le _ _).trans (by linarith only [hE,hF])
  rw [kernel,norm_div,norm_mul]
  calc
    _ ≤ (2*Real.exp (-t/2))/
        (‖1-Complex.exp (-(t : ℂ))‖*‖1-Complex.exp (-(a*(t : ℂ)))‖) :=
      div_le_div_of_nonneg_right hN (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (2*Real.exp (-t/2))/d^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd) hD
    _ = _ := by ring

#print axioms deriv_evenCylinder_zero
#print axioms evenCylinder_expansion
#print axioms analyticAt_cylinderRemainder_zero
#print axioms analyticAt_cylinderRemainder
#print axioms kernel_decomposition
#print axioms analyticAt_regularKernel_period
#print axioms continuousAt_regularKernel
#print axioms regularKernel_uniform_bound
#print axioms analyticAt_kernel_period
#print axioms continuousAt_kernel
#print axioms kernel_uniform_tail_bound
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringKernel
