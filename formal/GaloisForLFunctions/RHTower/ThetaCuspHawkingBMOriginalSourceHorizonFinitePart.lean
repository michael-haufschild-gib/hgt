import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceIncomingSubtraction

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

theorem sourceActionRemainder_continuousOn (s chi amp J K w : ℂ) (hs : w-2*s≠0) :
    ContinuousOn (sourceActionRemainder s chi amp J K w) (Ioo (0:ℝ) 1) := by
  refine ContinuousOn.congr ?_ (fun z hz => sourceActionRemainder_eq_original_subtraction s chi amp J K w hs hz)
  intro z hz
  have hN := (normalizable_derivatives_continued (w:=w) (chi:=chi) hz).1.continuousAt
  have hP := (power_derivatives (w/2) hz.1).1.continuousAt
  have hW := (power_derivatives w hz.1).1.continuousAt
  have hS : ContinuousAt (sourceProfile s w amp J K 1) z :=
    hP.mul (sourceRemainder_continuous s w amp J K 1).continuousAt
  have hxt : ContinuousAt tortoiseOf z := by
    unfold tortoiseOf
    have hsz : 0<Real.sqrt z := Real.sqrt_pos.mpr hz.1
    fun_prop (disch := positivity)
  have hX : ContinuousAt (fun t : ℝ => (tortoiseOf t:ℂ)) z := by fun_prop
  have hL : ContinuousAt (fun t : ℝ => (Real.log t:ℂ)) z := by
    fun_prop (disch := exact hz.1.ne')
  exact (((hN.mul hS).mul ((hX.mul continuousAt_const).add continuousAt_const)).sub
    (((continuousAt_const.mul hW).mul continuousAt_const).mul
      ((((hL.div_const 2).sub continuousAt_const).mul continuousAt_const).add continuousAt_const))).continuousWithinAt

/-- The admitted remainder of the actual source-action horizon integral. -/
def sourceActionHorizonRemainder (s chi amp J K w : ℂ) : ℂ :=
  ∫ z in Ioc (0:ℝ) (1/2),sourceActionRemainder s chi amp J K w z

/-- Holomorphy follows from the source-derived subtracted Cauchy bound;
 neither integrability nor a parameter-derivative bound is supplied. -/
theorem sourceActionHorizonRemainder_differentiableAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    DifferentiableAt ℂ (sourceActionHorizonRemainder s chi amp J K) w := by
  obtain ⟨R,C,β,hR,hC,hβ,hnear,hB⟩ := sourceActionRemainder_uniform_bound s chi amp J K w hw hwr hs
  let F : ℂ→ℝ→ℂ := fun u => (Ioc (0:ℝ) (1/2)).indicator (sourceActionRemainder s chi amp J K u)
  let bound : ℝ→ℝ := (Ioc (0:ℝ) (1/2)).indicator (fun z => C*(z^(β+1)+z^(-(1/2:ℝ))))
  have hinside (z : ℝ) (hz : z∈Ioc (0:ℝ) (1/2)) : z∈Ioo (0:ℝ) 1 := ⟨hz.1,by linarith [hz.2]⟩
  have hmeas (u : ℂ) (hu : u∈ball w R) : AEStronglyMeasurable (F u) volume := by
    apply (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
    exact ((sourceActionRemainder_continuousOn s chi amp J K u (hnear u hu).2).mono
      (fun z hz => hinside z hz)).aestronglyMeasurable measurableSet_Ioc
  have hdiff (z : ℝ) : DifferentiableOn ℂ (fun u => F u z) (ball w R) := by
    intro u hu
    by_cases hz : z∈Ioc (0:ℝ) (1/2)
    · simp only [F,indicator_of_mem hz]
      exact (sourceActionRemainder_frequency_analyticAt s chi amp J K u (hnear u hu).1
        (hnear u hu).2 (hinside z hz)).differentiableAt.differentiableWithinAt
    · simp only [F,indicator_of_notMem hz]
      fun_prop
  have hbound (z : ℝ) (u : ℂ) (hu : u∈ball w R) : ‖F u z‖≤bound z := by
    by_cases hz : z∈Ioc (0:ℝ) (1/2)
    · simpa only [F,bound,indicator_of_mem hz] using hB u hu z hz
    · simp only [F,bound,indicator_of_notMem hz,norm_zero,le_refl]
  have hBI : Integrable bound volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    have hp : IntegrableOn (fun z : ℝ => z^(β+1)) (Ioc (0:ℝ) (1/2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1/2)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<β+1))
    have hq : IntegrableOn (fun z : ℝ => z^(-(1/2:ℝ))) (Ioc (0:ℝ) (1/2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1/2)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1/2:ℝ)))
    exact (hp.add hq).const_mul C
  have h := differentiableAt_integral_of_cauchy_dominated hR hmeas hdiff hbound hBI
  simpa only [F,sourceActionHorizonRemainder,integral_indicator measurableSet_Ioc] using! h

theorem sourceActionHorizonRemainder_analyticAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    AnalyticAt ℂ (sourceActionHorizonRemainder s chi amp J K) w := by
  have hopen : IsOpen {u : ℂ | u.im≠0 ∧ -2<u.re ∧ u-2*s≠0} :=
    (isOpen_ne.preimage Complex.continuous_im).inter
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_ne.preimage (show Continuous (fun u : ℂ => u-2*s) by fun_prop)))
  have hd : DifferentiableOn ℂ (sourceActionHorizonRemainder s chi amp J K)
      {u : ℂ | u.im≠0 ∧ -2<u.re ∧ u-2*s≠0} := by
    intro u hu
    exact (sourceActionHorizonRemainder_differentiableAt s chi amp J K u hu.1 hu.2.1 hu.2.2).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds ⟨hw,hwr,hs⟩)

/-- The differentiated primitive of the original incoming source at the
 fixed interface one half, including its log-two finite constant. -/
def sourceActionIncomingPrimitive (s chi amp J K w : ℂ) (z : ℝ) : ℂ :=
  sourceReaderIncomingCoefficient w chi*sourceRemainder s w amp J K 1 0*power (w+1) z*
    ((((Real.log z:ℂ)/2-(Real.log 2:ℂ))*continuedOnset s w)/(w+1)-
      continuedOnset s w/(2*(w+1)^2)+deriv (continuedOnset s) w/(w+1))

def sourceActionHorizonPrimitive (s chi amp J K w : ℂ) : ℂ :=
  sourceActionIncomingPrimitive s chi amp J K w (1/2)

theorem sourceActionHorizonPrimitive_analyticAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hs : w-2*s≠0) :
    AnalyticAt ℂ (sourceActionHorizonPrimitive s chi amp J K) w := by
  have hw1 : w+1≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact hw (by simpa only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] using hi)
  have hA := normalizable_horizonRegularCoefficient_analyticAt w chi hw
  have hR := (sourceRemainder_frequency_entire s amp J K 1 0).analyticAt w
  have hP := ((power_exponent_entire (by norm_num : (0:ℝ)<1/2)).comp
    (show Differentiable ℂ (fun u : ℂ => u+1) by fun_prop)).analyticAt w
  have hT := continuedOnset_analyticAt s w hs
  have hD : AnalyticAt ℂ (fun u : ℂ => u+1) w := analyticAt_id.add analyticAt_const
  have hden : 2*(w+1)^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hw1)
  have hB : AnalyticAt ℂ (fun u : ℂ =>
      (((Real.log (1/2:ℝ):ℂ)/2-(Real.log 2:ℂ))*continuedOnset s u)/(u+1)-
        continuedOnset s u/(2*(u+1)^2)+deriv (continuedOnset s) u/(u+1)) w :=
    (((analyticAt_const.mul hT).div hD hw1).sub
      (hT.div (analyticAt_const.mul (hD.pow 2)) hden)).add (hT.deriv.div hD hw1)
  simpa only [sourceActionHorizonPrimitive,sourceActionIncomingPrimitive,sourceReaderIncomingCoefficient,Function.comp_def] using!
    (((hA.mul hR).mul hP).mul hB)

/-- The source-derived horizon finite part with its original leading
 counterterm restored; no connection denominator occurs in this value. -/
def sourceDerivativeHorizonFinitePart (s chi amp J K w : ℂ) : ℂ :=
  sourceActionHorizonPrimitive s chi amp J K w+sourceActionHorizonRemainder s chi amp J K w

theorem sourceDerivativeHorizonFinitePart_analyticAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    AnalyticAt ℂ (sourceDerivativeHorizonFinitePart s chi amp J K) w :=
  (sourceActionHorizonPrimitive_analyticAt s chi amp J K w hw hs).add
    (sourceActionHorizonRemainder_analyticAt s chi amp J K w hw hwr hs)

/-- Absolute admission of the actual horizon remainder in the full strip. -/
theorem sourceActionRemainder_integrable (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    IntegrableOn (sourceActionRemainder s chi amp J K w) (Ioc (0:ℝ) (1/2)) := by
  obtain ⟨R,C,β,hR,_,hβ,_,hB⟩ := sourceActionRemainder_uniform_bound s chi amp J K w hw hwr hs
  have hp : IntegrableOn (fun z : ℝ => z^(β+1)) (Ioc (0:ℝ) (1/2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1/2)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<β+1))
  have hq : IntegrableOn (fun z : ℝ => z^(-(1/2:ℝ))) (Ioc (0:ℝ) (1/2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1/2)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1/2:ℝ)))
  refine ((hp.add hq).const_mul C).mono' ?_ ?_
  · exact ((sourceActionRemainder_continuousOn s chi amp J K w hs).mono
      (fun z hz => ⟨hz.1,by linarith [hz.2]⟩)).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact hB w (mem_ball_self hR) z hz

/-- Actual leading incoming density of the source derivative. -/
def sourceActionIncomingDensity (s chi amp J K w : ℂ) (z : ℝ) : ℂ :=
  sourceReaderIncomingCoefficient w chi*power w z*sourceRemainder s w amp J K 1 0*
    (((Real.log z:ℂ)/2-(Real.log 2:ℂ))*continuedOnset s w+deriv (continuedOnset s) w)

theorem sourceActionDensity_eq_remainder_add (s chi amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w=
      sourceActionRemainder s chi amp J K w z+sourceActionIncomingDensity s chi amp J K w z := by
  rw [sourceActionRemainder_eq_original_subtraction s chi amp J K w hs hz,
    continuedSourceProfile_frequency_deriv s amp J K w hs hz]
  dsimp only [sourceActionIncomingDensity]
  ring

theorem sourceActionIncomingDensity_continuousOn (s chi amp J K w : ℂ) :
    ContinuousOn (sourceActionIncomingDensity s chi amp J K w) (Ioi (0:ℝ)) := by
  intro z hz
  have hP := (power_derivatives w hz).1.continuousAt
  have hL : ContinuousAt (fun t : ℝ => (Real.log t:ℂ)) z := by fun_prop (disch := exact hz.ne')
  exact (((continuousAt_const.mul hP).mul continuousAt_const).mul
    ((((hL.div_const 2).sub continuousAt_const).mul continuousAt_const).add continuousAt_const)).continuousWithinAt

/-- The prescribed source counterterm is the genuine primitive of its
 literal leading density, with the original finite normalization. -/
theorem sourceActionIncomingPrimitive_hasDerivAt (s chi amp J K w : ℂ)
    (hw1 : w+1≠0) {z : ℝ} (hz : 0<z) :
    HasDerivAt (sourceActionIncomingPrimitive s chi amp J K w)
      (sourceActionIncomingDensity s chi amp J K w z) z := by
  let A := sourceReaderIncomingCoefficient w chi*sourceRemainder s w amp J K 1 0
  let T := continuedOnset s w
  let D := deriv (continuedOnset s) w
  let L : ℂ := (Real.log 2:ℂ)
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hP := ((power_derivatives (w+1) hz).1).const_mul A
  have hL : HasDerivAt (fun t : ℝ => (Real.log t:ℂ)) (1/(z:ℂ)) z := by
    simpa only [Complex.ofReal_inv,one_div] using! (Real.hasDerivAt_log hz.ne').ofReal_comp
  have hB := (((((hL.div_const 2).sub_const L).mul_const T).div_const (w+1)).sub_const
    (T/(2*(w+1)^2))).add_const (D/(w+1))
  have h := hP.mul hB
  change HasDerivAt (sourceActionIncomingPrimitive s chi amp J K w) _ z at h
  apply h.congr_deriv
  have hp : power (w+1) z=power w z*(z:ℂ) := by
    rw [power,Complex.cpow_add _ _ hz0,Complex.cpow_one]
    rfl
  dsimp only [powerFirst,sourceActionIncomingDensity,A,T,D,L]
  rw [hp]
  field_simp [hz0,hw1]
  ring

/-- The actual differentiated-source cutoff, with exactly its incoming
 power/log counterterm restored. -/
def sourceDerivativeHorizonCutoff (s chi amp J K w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..(1/2:ℝ),normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w)+
    sourceActionIncomingPrimitive s chi amp J K w e

theorem sourceDerivativeHorizonCutoff_eq (s chi amp J K w : ℂ)
    (hw1 : w+1≠0) (hs : w-2*s≠0) {e : ℝ} (he : 0<e) (heb : e≤1/2) :
    sourceDerivativeHorizonCutoff s chi amp J K w e=
      sourceActionHorizonPrimitive s chi amp J K w+
        (∫ z in e..(1/2:ℝ),sourceActionRemainder s chi amp J K w z) := by
  have hsub : uIcc e (1/2:ℝ)⊆Ioo (0:ℝ) 1 := by
    rw [uIcc_of_le heb]
    intro z hz
    exact ⟨he.trans_le hz.1,by linarith [hz.2]⟩
  have hR : IntervalIntegrable (sourceActionRemainder s chi amp J K w) volume e (1/2:ℝ) :=
    ((sourceActionRemainder_continuousOn s chi amp J K w hs).mono hsub).intervalIntegrable
  have hD : IntervalIntegrable (sourceActionIncomingDensity s chi amp J K w) volume e (1/2:ℝ) :=
    ((sourceActionIncomingDensity_continuousOn s chi amp J K w).mono (fun z hz => (hsub hz).1)).intervalIntegrable
  have hP := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z hz => sourceActionIncomingPrimitive_hasDerivAt s chi amp J K w hw1 (hsub hz).1) hD
  have hI : (∫ z in e..(1/2:ℝ),normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w)=
      (∫ z in e..(1/2:ℝ),sourceActionRemainder s chi amp J K w z)+
        ∫ z in e..(1/2:ℝ),sourceActionIncomingDensity s chi amp J K w z := by
    rw [← intervalIntegral.integral_add hR hD]
    apply intervalIntegral.integral_congr_uIoo
    intro z hz
    rw [uIoo_of_le heb] at hz
    exact sourceActionDensity_eq_remainder_add s chi amp J K w hs ⟨he.trans hz.1,by linarith [hz.2]⟩
  rw [sourceDerivativeHorizonCutoff,hI,hP,sourceActionHorizonPrimitive]
  ring

/-- The holomorphic horizon value is the limit of the original source
 cutoff, including its fixed power/log finite constant. -/
theorem sourceDerivativeHorizonCutoff_tendsto (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    Tendsto (sourceDerivativeHorizonCutoff s chi amp J K w) (𝓝[>] (0:ℝ))
      (𝓝 (sourceDerivativeHorizonFinitePart s chi amp J K w)) := by
  have hw1 : w+1≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact hw (by simpa only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] using hi)
  have hRI := sourceActionRemainder_integrable s chi amp J K w hw hwr hs
  have hRcc : IntegrableOn (sourceActionRemainder s chi amp J K w) (uIcc (0:ℝ) (1/2)) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1/2),integrableOn_Icc_iff_integrableOn_Ioc]
    exact hRI
  have hc := (intervalIntegral.continuousOn_primitive_interval_left hRcc) (0:ℝ) left_mem_uIcc
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1/2)] at hc
  have hh := hc.mono (show Ioo (0:ℝ) (1/2)⊆Icc (0:ℝ) (1/2) from Ioo_subset_Icc_self)
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0:ℝ)<1/2)] at hh
  have hlim := hh.const_add (sourceActionHorizonPrimitive s chi amp J K w)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2)] at hlim
  change Tendsto (fun e : ℝ => sourceActionHorizonPrimitive s chi amp J K w+
    ∫ z in e..(1/2:ℝ),sourceActionRemainder s chi amp J K w z) _
      (𝓝 (sourceDerivativeHorizonFinitePart s chi amp J K w)) at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with e he
  exact (sourceDerivativeHorizonCutoff_eq s chi amp J K w hw1 hs he.1 he.2.le).symm

end
end RHTower.D4BMOriginalSourceResolvent
