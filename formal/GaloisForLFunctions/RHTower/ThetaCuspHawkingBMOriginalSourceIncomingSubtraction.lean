import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceActionReduction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRegularOuterPairing

/-!
# Original source subtraction through the physical QNM strip

The independent source and normalizable reader expose the actual incoming
coefficient. Subtracting it gives a locally uniform integrable remainder
for real frequency part greater than minus two. Cauchy estimates control
the source derivative on the same strip. Its explicit leading term retains
the original log-two offset and fixes all angular data.
-/

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource
noncomputable section
set_option autoImplicit false

/-- The incoming coefficient of the unchanged normalizable reader. -/
def sourceReaderIncomingCoefficient (v chi : ℂ) : ℂ :=
  horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)

/-- Only the actual leading incoming source density is subtracted. -/
def incomingSourceTerm (s chi amp J K u v : ℂ) (z : ℝ) : ℂ :=
  sourceReaderIncomingCoefficient v chi*power ((u+v)/2) z*
    sourceRemainder s u amp J K 1 0*continuedOnset s u

def incomingSubtractedSource (s chi amp J K u v : ℂ) (z : ℝ) : ℂ :=
  normalizable v chi z*continuedSourceProfile s amp J K u z-
    incomingSourceTerm s chi amp J K u v z

/-- Independent source and reader frequencies expose the exact first
 incoming remainder while retaining the entire opposite branch. -/
theorem incomingSubtractedSource_decomposition (s chi amp J K u v : ℂ)
    (hv : v.im≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    incomingSubtractedSource s chi amp J K u v z=
      sourceReaderIncomingCoefficient v chi*power ((u+v)/2) z*
        (gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z-
          sourceRemainder s u amp J K 1 0)*continuedOnset s u+
      (connection v chi/(2*v))*power ((u-v)/2) z*
        gaussFactor (-v) chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u := by
  have hn := (original_homogeneous_horizon_representation v chi hv
    (fun z hz => (normalizable_derivatives_continued hz).1)
    (fun z hz => (normalizable_derivatives_continued hz).2)
    (fun z hz => normalizable_equation_continued hz) hz).1
  rw [normalizable_opposite_coefficient v chi hv] at hn
  have hS : continuedSourceProfile s amp J K u z=
      power (u/2) z*sourceRemainder s u amp J K 1 z*continuedOnset s u := by
    dsimp only [continuedSourceProfile,sourceProfile,sourceRemainder,continuedOnset]
    ring
  have hmul (a : ℂ) : power (a/2) z*power (u/2) z=power ((u+a)/2) z := by
    rw [power,power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.1.ne')]
    congr 1
    ring
  have hm := hmul (-v)
  rw [show u+-v=u-v by ring] at hm
  unfold incomingSubtractedSource
  rw [hn,hS]
  dsimp only [incomingSourceTerm,sourceReaderIncomingCoefficient,horizon,dress]
  linear_combination
    horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)*
      gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u*(hmul v)+
    (connection v chi/(2*v))*gaussFactor (-v) chi false (z:ℂ)*
      sourceRemainder s u amp J K 1 z*continuedOnset s u*hm

/-- After the actual incoming coefficient is removed, a locally uniform
integrable power controls independent source/reader frequencies throughout
 the physical continuation strip. No endpoint estimate is assumed. -/
theorem incomingSubtractedSource_uniform_bound (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    ∃ R C β : ℝ,0<R ∧ 0≤C ∧ -2<β ∧
      (∀ u∈ball w R,u.im≠0 ∧ u-2*s≠0) ∧
      ∀ u∈ball w R,∀ v∈ball w R,∀ z∈Ioc (0:ℝ) (1/2),
        ‖incomingSubtractedSource s chi amp J K u v z‖≤
          C*(z^(β+1)+z^(-(1/2:ℝ))) := by
  let A := fun v => sourceReaderIncomingCoefficient v chi
  let beta := fun v => connection v chi/(2*v)
  let MA := ‖A w‖+1
  let MB := ‖beta w‖+1
  let MT := ‖continuedOnset s w‖+1
  have hMA : 0≤MA := by dsimp [MA];positivity
  have hMB : 0≤MB := by dsimp [MB];positivity
  have hMT : 0≤MT := by dsimp [MT];positivity
  have hw0 : w≠0 := by intro he;exact hw (by simp [he])
  have hAc : ContinuousAt A w := (normalizable_horizonRegularCoefficient_analyticAt w chi hw).continuousAt
  have hBc : ContinuousAt beta w := (connection_frequency_analyticAt w chi hw).continuousAt.div
    (show ContinuousAt (fun v : ℂ => 2*v) w by fun_prop) (mul_ne_zero (by norm_num) hw0)
  have hTc := (continuedOnset_analyticAt s w hs).continuousAt
  have hn : ∀ᶠ u : ℂ in 𝓝 w,u.im≠0 ∧ u-2*s≠0 ∧ ‖A u‖≤MA ∧ ‖beta u‖≤MB ∧ ‖continuedOnset s u‖≤MT := by
    filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hw,
      (show ContinuousAt (fun u : ℂ => u-2*s) w by fun_prop).eventually_ne hs,
      hAc.norm.eventually_lt continuousAt_const (lt_add_one ‖A w‖),
      hBc.norm.eventually_lt continuousAt_const (lt_add_one ‖beta w‖),
      hTc.norm.eventually_lt continuousAt_const (lt_add_one ‖continuedOnset s w‖)] with u hi hs hA hB hT
    exact ⟨hi,hs,hA.le,hB.le,hT.le⟩
  obtain ⟨R0,hR0,h0⟩ := Metric.eventually_nhds_iff.mp hn
  obtain ⟨RP,CP,hRP,hCP,hGP⟩ := horizonGauss_uniform_first_bound w chi hw
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨RM,CM,hRM,hCM,hGM⟩ := horizonGauss_uniform_first_bound (-w) chi
    (by simpa only [Complex.neg_im,neg_ne_zero] using hw)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨CR,hCR,hSR⟩ := sourceRemainder_uniform_first_bound s w amp J K 1
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨M0,hM0⟩ := ((isCompact_closedBall w 1).prod
    (isCompact_Icc : IsCompact (Icc (0:ℝ) (1/2)))).exists_bound_of_continuousOn
      (sourceRemainder_joint_continuous s amp J K 1).continuousOn
  let M := max M0 0
  have hM : 0≤M := le_max_right _ _
  let R := min R0 (min RP (min RM (min (1/4) ((w.re+2)/4))))
  let β := (w.re-2)/2
  have hR : 0<R := lt_min hR0 (lt_min hRP (lt_min hRM (lt_min (by norm_num) (by linarith))))
  have hR0' : R≤R0 := min_le_left _ _
  have hRP' : R≤RP := (min_le_right _ _).trans (min_le_left _ _)
  have hRM' : R≤RM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRend : R ≤ min (1/4) ((w.re+2)/4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRq : R≤1/4 := hRend.trans (min_le_left _ _)
  have hRs : R≤(w.re+2)/4 := hRend.trans (min_le_right _ _)
  have hR1 : R≤1 := by linarith
  have hβ : -2<β := by dsimp [β];linarith
  have hnear (u : ℂ) (hu : u∈ball w R) := h0 ((mem_ball.mp hu).trans_le hR0')
  let C1 := MA*(CP*M+CR)*MT
  let C2 := MB*(CM+1)*M*MT
  have hC1 : 0≤C1 := by dsimp [C1];positivity
  have hC2 : 0≤C2 := by dsimp [C2];positivity
  refine ⟨R,C1+C2,β,hR,add_nonneg hC1 hC2,hβ,fun u hu => ⟨(hnear u hu).1,(hnear u hu).2.1⟩,?_⟩
  intro u hu v hv z hz
  have hz0 : 0≤z := hz.1.le
  have hz1 : z≤1 := by linarith [hz.2]
  have hzI : z∈Ioo (0:ℝ) 1 := ⟨hz.1,by linarith [hz.2]⟩
  have hzC : z∈Icc (0:ℝ) (1/2) := ⟨hz.1.le,hz.2⟩
  have hS : ‖sourceRemainder s u amp J K 1 z‖≤M :=
    (hM0 (u,z) ⟨ball_subset_closedBall (ball_subset_ball hR1 hu),hzC⟩).trans (le_max_left _ _)
  have hSR' := hSR u (ball_subset_ball hR1 hu) z hzC
  have hpG := hGP v (ball_subset_ball hRP' hv) z hzC
  have hmG := hGM (-v) (by simpa only [mem_ball,dist_neg_neg] using
    (ball_subset_ball hRM' hv)) z hzC
  have hgm : ‖gaussFactor (-v) chi false (z:ℂ)‖≤CM+1 := by
    have hn := norm_sub_norm_le (gaussFactor (-v) chi false (z:ℂ)) (1:ℂ)
    rw [norm_one] at hn
    linarith [mul_le_mul_of_nonneg_left hz1 hCM]
  have hcore : ‖gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z-
      sourceRemainder s u amp J K 1 0‖≤(CP*M+CR)*z := by
    rw [show gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z-
      sourceRemainder s u amp J K 1 0=
      (gaussFactor v chi false (z:ℂ)-1)*sourceRemainder s u amp J K 1 z+
      (sourceRemainder s u amp J K 1 z-sourceRemainder s u amp J K 1 0) by ring]
    calc
      _≤‖(gaussFactor v chi false (z:ℂ)-1)*sourceRemainder s u amp J K 1 z‖+
        ‖sourceRemainder s u amp J K 1 z-sourceRemainder s u amp J K 1 0‖ := norm_add_le _ _
      _≤(CP*z)*M+CR*z := by rw [norm_mul];gcongr
      _=(CP*M+CR)*z := by ring
  have hreal (a : ℂ) (ha : a∈ball w R) : |a.re-w.re|<R := by
    have hn := (Complex.abs_re_le_norm (a-w)).trans_lt (show ‖a-w‖<R by simpa only [dist_eq_norm] using mem_ball.mp ha)
    simpa only [Complex.sub_re] using hn
  have hpRe : β≤((u+v)/2).re := by
    simp only [Complex.div_ofNat_re,Complex.add_re]
    dsimp only [β]
    linarith [(abs_lt.mp (hreal u hu)).1,(abs_lt.mp (hreal v hv)).1]
  have hmRe : -(1/2:ℝ)≤((u-v)/2).re := by
    simp only [Complex.div_ofNat_re,Complex.sub_re]
    linarith [(abs_lt.mp (hreal u hu)).1,(abs_lt.mp (hreal v hv)).2]
  have hpBound : ‖power ((u+v)/2) z‖≤z^β := by
    rw [power,Complex.norm_cpow_eq_rpow_re_of_pos hz.1]
    exact Real.rpow_le_rpow_of_exponent_ge hz.1 hz1 hpRe
  have hmBound : ‖power ((u-v)/2) z‖≤z^(-(1/2:ℝ)) := by
    rw [power,Complex.norm_cpow_eq_rpow_re_of_pos hz.1]
    exact Real.rpow_le_rpow_of_exponent_ge hz.1 hz1 hmRe
  have hA := (hnear v hv).2.2.1
  have hB := (hnear v hv).2.2.2.1
  have hT := (hnear u hu).2.2.2.2
  rw [incomingSubtractedSource_decomposition s chi amp J K u v (hnear v hv).1 hzI]
  calc
    _≤‖sourceReaderIncomingCoefficient v chi*power ((u+v)/2) z*
      (gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z-
        sourceRemainder s u amp J K 1 0)*continuedOnset s u‖+
      ‖(connection v chi/(2*v))*power ((u-v)/2) z*gaussFactor (-v) chi false (z:ℂ)*
        sourceRemainder s u amp J K 1 z*continuedOnset s u‖ := norm_add_le _ _
    _≤MA*z^β*((CP*M+CR)*z)*MT+MB*z^(-(1/2:ℝ))*(CM+1)*M*MT := by
      simp only [norm_mul]
      dsimp only [A,beta] at hA hB
      gcongr
    _=C1*z^(β+1)+C2*z^(-(1/2:ℝ)) := by
      rw [Real.rpow_add hz.1,Real.rpow_one]
      dsimp only [C1,C2]
      ring
    _≤(C1+C2)*(z^(β+1)+z^(-(1/2:ℝ))) := by
      nlinarith [Real.rpow_nonneg hz.1.le (β+1),Real.rpow_nonneg hz.1.le (-(1/2:ℝ)),
        mul_nonneg hC1 (Real.rpow_nonneg hz.1.le (-(1/2:ℝ))),
        mul_nonneg hC2 (Real.rpow_nonneg hz.1.le (β+1))]

/-- The leading source profile keeps the literal horizon coefficient and
 unchanged onset before the reader is applied. -/
def sourceIncomingLeadingProfile (s amp J K u : ℂ) (z : ℝ) : ℂ :=
  power (u/2) z*sourceRemainder s u amp J K 1 0*continuedOnset s u

theorem sourceIncomingLeadingProfile_frequency_analyticAt (s amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : 0<z) :
    AnalyticAt ℂ (fun u => sourceIncomingLeadingProfile s amp J K u z) w := by
  have hP := ((power_exponent_entire hz).comp
    (show Differentiable ℂ (fun u : ℂ => u/2) by fun_prop)).analyticAt w
  have hR := (sourceRemainder_frequency_entire s amp J K 1 0).analyticAt w
  have hT := continuedOnset_analyticAt s w hs
  simpa only [sourceIncomingLeadingProfile,Function.comp_def] using! (hP.mul hR).mul hT

theorem incomingSourceTerm_factor (s chi amp J K u v : ℂ) {z : ℝ} (hz : 0<z) :
    incomingSourceTerm s chi amp J K u v z=
      sourceReaderIncomingCoefficient v chi*power (v/2) z*sourceIncomingLeadingProfile s amp J K u z := by
  have hp : power (v/2) z*power (u/2) z=power ((u+v)/2) z := by
    rw [power,power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.ne')]
    congr 1
    ring
  dsimp only [incomingSourceTerm,sourceIncomingLeadingProfile]
  rw [← hp]
  ring

private theorem incomingSubtractedSource_function_eq (s chi amp J K v : ℂ)
    {z : ℝ} (hz : 0<z) :
    (fun u => incomingSubtractedSource s chi amp J K u v z)=
    (fun u => normalizable v chi z*continuedSourceProfile s amp J K u z-
      (sourceReaderIncomingCoefficient v chi*power (v/2) z)*sourceIncomingLeadingProfile s amp J K u z) := by
  funext u
  rw [incomingSubtractedSource,incomingSourceTerm_factor s chi amp J K u v hz]

theorem incomingSubtractedSource_source_analyticAt (s chi amp J K w v : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : 0<z) :
    AnalyticAt ℂ (fun u => incomingSubtractedSource s chi amp J K u v z) w := by
  rw [incomingSubtractedSource_function_eq s chi amp J K v hz]
  exact (analyticAt_const.mul (continuedSourceProfile_frequency_analyticAt s amp J K w hs hz)).sub
    (analyticAt_const.mul (sourceIncomingLeadingProfile_frequency_analyticAt s amp J K w hs hz))

/-- The actual source derivative after the original leading incoming
 source term is subtracted. No derivative of the reader is taken. -/
def sourceActionRemainder (s chi amp J K w : ℂ) (z : ℝ) : ℂ :=
  normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w-
    (sourceReaderIncomingCoefficient w chi*power (w/2) z)*
      deriv (fun u => sourceIncomingLeadingProfile s amp J K u z) w

theorem incomingSubtractedSource_diagonal_source_deriv (s chi amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : 0<z) :
    deriv (fun u => incomingSubtractedSource s chi amp J K u w z) w=
      sourceActionRemainder s chi amp J K w z := by
  rw [incomingSubtractedSource_function_eq s chi amp J K w hz]
  have hD := ((continuedSourceProfile_frequency_analyticAt s amp J K w hs hz).differentiableAt.hasDerivAt.const_mul
    (normalizable w chi z)).sub
      ((sourceIncomingLeadingProfile_frequency_analyticAt s amp J K w hs hz).differentiableAt.hasDerivAt.const_mul
        (sourceReaderIncomingCoefficient w chi*power (w/2) z))
  exact hD.deriv

theorem sourceActionRemainder_frequency_analyticAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hs : w-2*s≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => sourceActionRemainder s chi amp J K u z) w := by
  have hN := (normalizable_frequency_entire chi hz).analyticAt w
  have hS := (continuedSourceProfile_frequency_analyticAt s amp J K w hs hz.1).deriv
  have hA := normalizable_horizonRegularCoefficient_analyticAt w chi hw
  have hP := ((power_exponent_entire hz.1).comp
    (show Differentiable ℂ (fun u : ℂ => u/2) by fun_prop)).analyticAt w
  have hL := (sourceIncomingLeadingProfile_frequency_analyticAt s amp J K w hs hz.1).deriv
  simpa only [sourceActionRemainder,sourceReaderIncomingCoefficient,Function.comp_def] using!
    (hN.mul hS).sub ((hA.mul hP).mul hL)

/-- Cauchy estimates on the source variable give the actual subtracted
 derivative an integrable bound throughout the physical continuation strip. -/
theorem sourceActionRemainder_uniform_bound (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    ∃ R C β : ℝ,0<R ∧ 0≤C ∧ -2<β ∧
      (∀ u∈ball w R,u.im≠0 ∧ u-2*s≠0) ∧
      ∀ u∈ball w R,∀ z∈Ioc (0:ℝ) (1/2),
        ‖sourceActionRemainder s chi amp J K u z‖≤C*(z^(β+1)+z^(-(1/2:ℝ))) := by
  obtain ⟨R,C,β,hR,hC,hβ,hnear,hB⟩ := incomingSubtractedSource_uniform_bound s chi amp J K w hw hwr hs
  have hsub : ball w (R/2)⊆ball w R := ball_subset_ball (by linarith)
  refine ⟨R/2,2*C/R,β,half_pos hR,by positivity,hβ,fun u hu => hnear u (hsub hu),?_⟩
  intro v hv z hz
  have hdiff : DifferentiableOn ℂ (fun u => incomingSubtractedSource s chi amp J K u v z) (ball w R) := by
    intro u hu
    exact (incomingSubtractedSource_source_analyticAt s chi amp J K u v (hnear u hu).2 hz.1).differentiableAt.differentiableWithinAt
  have hbound : ∀ u∈ball w R,‖incomingSubtractedSource s chi amp J K u v z‖≤C*(z^(β+1)+z^(-(1/2:ℝ))) :=
    fun u hu => hB u hu v (hsub hv) z hz
  have hc := Bottcher.norm_deriv_le_of_bounded_on_ball hR hdiff hbound v hv
  rw [incomingSubtractedSource_diagonal_source_deriv s chi amp J K v (hnear v (hsub hv)).2 hz.1] at hc
  convert hc using 1
  ring

/-- The leading incoming source retains the exact original log-two offset. -/
theorem sourceIncomingBareProfile_exp (s amp J K w : ℂ) {z : ℝ} (hz : 0<z) :
    power (w/2) z*sourceRemainder s w amp J K 1 0=
      Complex.exp (w*((Real.log z:ℂ)/2-(Real.log 2:ℂ)))*sourceRemainder s 0 amp J K 1 0 := by
  have hp : power (w/2) z*power (2*s-w) 2=
      Complex.exp (w*((Real.log z:ℂ)/2-(Real.log 2:ℂ)))*power (2*s) 2 := by
    unfold power
    simp only [Complex.ofReal_ofNat]
    have hl2 : Complex.log (2:ℂ)=(Real.log 2:ℂ) := by
      simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (by norm_num : (0:ℝ)≤2)).symm
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hz.ne'),
      Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
      Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
      ← Complex.exp_add,← Complex.exp_add,
      ← Complex.ofReal_log hz.le,hl2]
    congr 1
    ring
  simp only [sourceRemainder,Complex.ofReal_zero,sub_zero,Real.sqrt_one,
    show (1+1:ℝ)=2 by norm_num,one_mul,mul_one]
  linear_combination amp^2*
    (((5*s^2+15*s+4)/4)*J+s*(s-1)/4*((s+2)^2*J-K))*hp

/-- Exact derivative of the leading source; the original horizon shift is
 included in the finite counterterm rather than chosen afterward. -/
theorem sourceIncomingLeadingProfile_frequency_deriv (s amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : 0<z) :
    deriv (fun u => sourceIncomingLeadingProfile s amp J K u z) w=
      power (w/2) z*sourceRemainder s w amp J K 1 0*
        (((Real.log z:ℂ)/2-(Real.log 2:ℂ))*continuedOnset s w+deriv (continuedOnset s) w) := by
  let A := sourceRemainder s 0 amp J K 1 0
  let L : ℂ := (Real.log z:ℂ)/2-(Real.log 2:ℂ)
  have he : (fun u => sourceIncomingLeadingProfile s amp J K u z)=
      (fun u => Complex.exp (u*L)*A*continuedOnset s u) := by
    funext u
    rw [sourceIncomingLeadingProfile,sourceIncomingBareProfile_exp s amp J K u hz]
  have hd := (((hasDerivAt_id w).mul_const L).cexp.mul_const A).mul
    (continuedOnset_analyticAt s w hs).differentiableAt.hasDerivAt
  simp only [Pi.mul_def,id_eq,one_mul] at hd
  rw [he,hd.deriv,sourceIncomingBareProfile_exp s amp J K w hz]
  dsimp only [A,L]
  ring

/-- The subtracted derivative retains exactly the original logarithmic
 incoming term, with fixed angular and onset data. -/
theorem sourceActionRemainder_eq_original_subtraction (s chi amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    sourceActionRemainder s chi amp J K w z=
      normalizable w chi z*sourceProfile s w amp J K 1 z*
        ((tortoiseOf z:ℂ)*continuedOnset s w+deriv (continuedOnset s) w)-
      sourceReaderIncomingCoefficient w chi*power w z*sourceRemainder s w amp J K 1 0*
        (((Real.log z:ℂ)/2-(Real.log 2:ℂ))*continuedOnset s w+deriv (continuedOnset s) w) := by
  rw [sourceActionRemainder,continuedSourceProfile_frequency_deriv s amp J K w hs hz,
    sourceIncomingLeadingProfile_frequency_deriv s amp J K w hs hz.1]
  have hp : power (w/2) z*power (w/2) z=power w z := by
    rw [power,power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.1.ne')]
    congr 1
    ring
  rw [← hp]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
