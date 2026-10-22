import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalSourceHorizonFinitePart
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The source derivative keeps the reader, angular data and source rate fixed. -/
def sourceActionDensity (s chi amp J K w : ℂ) (z : ℝ) : ℂ :=
  normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w

theorem sourceActionDensity_continuousOn (s chi amp J K w : ℂ) (hs : w-2*s≠0) :
    ContinuousOn (sourceActionDensity s chi amp J K w) (Ioo (0:ℝ) 1) := by
  exact ((sourceActionRemainder_continuousOn s chi amp J K w hs).add
    ((sourceActionIncomingDensity_continuousOn s chi amp J K w).mono
      (fun _ hz => hz.1))).congr (fun z hz => sourceActionDensity_eq_remainder_add s chi amp J K w hs hz)

theorem sourceActionDensity_frequency_analyticAt (s chi amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => sourceActionDensity s chi amp J K u z) w :=
  ((normalizable_frequency_entire chi hz).analyticAt w).mul
    (continuedSourceProfile_frequency_analyticAt s amp J K w hs hz.1).deriv

/-- The explicit source factorization gives a common bound through the
 outer endpoint; no lower bound on the frequency real part is needed. -/
theorem sourceActionDensity_outer_uniform_bound (s chi amp J K w : ℂ) (hs : w-2*s≠0) :
    ∃ R C : ℝ, 0<R ∧ 0≤C ∧ (∀ u∈ball w R,u-2*s≠0) ∧
      ∀ u∈ball w R,∀ z∈Ioo (1/2:ℝ) 1,‖sourceActionDensity s chi amp J K u z‖≤C := by
  let MT := ‖continuedOnset s w‖+1
  let MD := ‖deriv (continuedOnset s) w‖+1
  have hMT : 0≤MT := by dsimp [MT]; positivity
  have hMD : 0≤MD := by dsimp [MD]; positivity
  have hT := continuedOnset_analyticAt s w hs
  have hnear : ∀ᶠ u : ℂ in 𝓝 w,u-2*s≠0 ∧ ‖continuedOnset s u‖≤MT ∧ ‖deriv (continuedOnset s) u‖≤MD := by
    filter_upwards [(show ContinuousAt (fun u : ℂ => u-2*s) w by fun_prop).eventually_ne hs,
      hT.continuousAt.norm.eventually_lt continuousAt_const (lt_add_one ‖continuedOnset s w‖),
      hT.deriv.continuousAt.norm.eventually_lt continuousAt_const (lt_add_one ‖deriv (continuedOnset s) w‖)] with u hu ht hd
    exact ⟨hu,ht.le,hd.le⟩
  obtain ⟨R0,hR0,h0⟩ := Metric.eventually_nhds_iff.mp hnear
  let R := min R0 1
  have hR : 0<R := lt_min hR0 (by norm_num)
  have hsmall (u : ℂ) (hu : u∈ball w R) := h0 ((mem_ball.mp hu).trans_le (min_le_left _ _))
  have hxc : ContinuousOn (fun z : ℝ => (tortoiseOf z:ℂ)) (Icc (1/2:ℝ) 1) := by
    intro z hz
    have hz0 : 0<z := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hz.1
    have hsz : 0<Real.sqrt z := Real.sqrt_pos.mpr hz0
    have hx : ContinuousAt tortoiseOf z := by
      unfold tortoiseOf
      fun_prop (disch := positivity)
    exact (show ContinuousAt (fun t : ℝ => (tortoiseOf t:ℂ)) z by fun_prop).continuousWithinAt
  obtain ⟨X0,hX0⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  let X := max X0 0
  have hX : 0≤X := le_max_right _ _
  obtain ⟨B,hB,hbare⟩ := outerSource_uniform_bound s chi amp J K w
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  refine ⟨R,B*(X*MT+MD),hR,by positivity,(fun u hu => (hsmall u hu).1),?_⟩
  intro u hu z hz
  have hSrc := hbare u (ball_subset_ball (min_le_right _ _) hu) z ⟨hz.1.le,hz.2.le⟩
  have hT' := (hsmall u hu).2.1
  have hD' := (hsmall u hu).2.2
  have hX' : ‖(tortoiseOf z:ℂ)‖≤X := (hX0 z ⟨hz.1.le,hz.2.le⟩).trans (le_max_left _ _)
  rw [sourceActionDensity,continuedSourceProfile_frequency_deriv s amp J K u (hsmall u hu).1
    ⟨by linarith [hz.1],hz.2⟩,← mul_assoc,norm_mul]
  apply mul_le_mul hSrc _ (norm_nonneg _) hB
  calc
    ‖(tortoiseOf z:ℂ)*continuedOnset s u+deriv (continuedOnset s) u‖
      ≤ ‖(tortoiseOf z:ℂ)‖*‖continuedOnset s u‖+‖deriv (continuedOnset s) u‖ := by
        simpa only [norm_mul] using norm_add_le ((tortoiseOf z:ℂ)*continuedOnset s u) (deriv (continuedOnset s) u)
    _ ≤ X*MT+MD := by gcongr

/-- The actual outer integral of the differentiated source. -/
def sourceDerivativeOuterIntegral (s chi amp J K w : ℂ) : ℂ :=
  ∫ z in Ioo (1/2:ℝ) 1,sourceActionDensity s chi amp J K w z

theorem sourceActionDensity_outer_integrable (s chi amp J K w : ℂ) (hs : w-2*s≠0) :
    IntegrableOn (sourceActionDensity s chi amp J K w) (Ioo (1/2:ℝ) 1) := by
  obtain ⟨R,C,hR,_,_,hB⟩ := sourceActionDensity_outer_uniform_bound s chi amp J K w hs
  have hi : IntegrableOn (fun _ : ℝ => C) (Ioo (1/2:ℝ) 1) := integrableOn_const (by simp)
  refine hi.mono' ?_ ?_
  · exact ((sourceActionDensity_continuousOn s chi amp J K w hs).mono
      (fun z hz => ⟨by linarith [hz.1],hz.2⟩)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hB w (mem_ball_self hR) z hz

theorem sourceDerivativeOuterIntegral_differentiableAt (s chi amp J K w : ℂ) (hs : w-2*s≠0) :
    DifferentiableAt ℂ (sourceDerivativeOuterIntegral s chi amp J K) w := by
  obtain ⟨R,C,hR,_,hnear,hB⟩ := sourceActionDensity_outer_uniform_bound s chi amp J K w hs
  let F : ℂ→ℝ→ℂ := fun u => (Ioo (1/2:ℝ) 1).indicator (sourceActionDensity s chi amp J K u)
  let bound : ℝ→ℝ := (Ioo (1/2:ℝ) 1).indicator (fun _ => C)
  have hinside (z : ℝ) (hz : z∈Ioo (1/2:ℝ) 1) : z∈Ioo (0:ℝ) 1 := ⟨by linarith [hz.1],hz.2⟩
  have hm (u : ℂ) (hu : u∈ball w R) : AEStronglyMeasurable (F u) volume := by
    apply (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr
    exact ((sourceActionDensity_continuousOn s chi amp J K u (hnear u hu)).mono
      (fun z hz => hinside z hz)).aestronglyMeasurable measurableSet_Ioo
  have hd (z : ℝ) : DifferentiableOn ℂ (fun u => F u z) (ball w R) := by
    intro u hu
    by_cases hz : z∈Ioo (1/2:ℝ) 1
    · simp only [F,indicator_of_mem hz]
      exact (sourceActionDensity_frequency_analyticAt s chi amp J K u (hnear u hu)
        (hinside z hz)).differentiableAt.differentiableWithinAt
    · simp only [F,indicator_of_notMem hz]
      fun_prop
  have hbound (z : ℝ) (u : ℂ) (hu : u∈ball w R) : ‖F u z‖≤bound z := by
    by_cases hz : z∈Ioo (1/2:ℝ) 1
    · simpa only [F,bound,indicator_of_mem hz] using hB u hu z hz
    · simp only [F,bound,indicator_of_notMem hz,norm_zero,le_refl]
  have hi : Integrable bound volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have h := differentiableAt_integral_of_cauchy_dominated hR hm hd hbound hi
  simpa only [F,sourceDerivativeOuterIntegral,integral_indicator measurableSet_Ioo] using! h

theorem sourceDerivativeOuterIntegral_analyticAt (s chi amp J K w : ℂ) (hs : w-2*s≠0) :
    AnalyticAt ℂ (sourceDerivativeOuterIntegral s chi amp J K) w := by
  have ho : IsOpen {u : ℂ | u-2*s≠0} := isOpen_ne.preimage (show Continuous (fun u : ℂ => u-2*s) by fun_prop)
  have hd : DifferentiableOn ℂ (sourceDerivativeOuterIntegral s chi amp J K) {u : ℂ | u-2*s≠0} :=
    fun u hu => (sourceDerivativeOuterIntegral_differentiableAt s chi amp J K u hu).differentiableWithinAt
  exact hd.analyticAt (ho.mem_nhds hs)

/-- The full differentiated-source action, with the original incoming finite constant. -/
def sourceDerivativeFinitePart (s chi amp J K w : ℂ) : ℂ :=
  sourceDerivativeHorizonFinitePart s chi amp J K w+sourceDerivativeOuterIntegral s chi amp J K w

theorem sourceDerivativeFinitePart_analyticAt (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    AnalyticAt ℂ (sourceDerivativeFinitePart s chi amp J K) w :=
  (sourceDerivativeHorizonFinitePart_analyticAt s chi amp J K w hw hwr hs).add
    (sourceDerivativeOuterIntegral_analyticAt s chi amp J K w hs)

/-- The full literal radial source cutoff retains exactly the same incoming primitive. -/
def sourceDerivativeCutoff (s chi amp J K w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..(1:ℝ),sourceActionDensity s chi amp J K w z)+
    sourceActionIncomingPrimitive s chi amp J K w e

theorem sourceDerivativeCutoff_eq (s chi amp J K w : ℂ) (hs : w-2*s≠0)
    {e : ℝ} (he : 0<e) (heb : e≤1/2) :
    sourceDerivativeCutoff s chi amp J K w e=
      sourceDerivativeHorizonCutoff s chi amp J K w e+sourceDerivativeOuterIntegral s chi amp J K w := by
  have hI : IntervalIntegrable (sourceActionDensity s chi amp J K w) volume e (1/2:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    apply (sourceActionDensity_continuousOn s chi amp J K w hs).mono
    rw [uIcc_of_le heb]
    exact fun z hz => ⟨he.trans_le hz.1,by linarith [hz.2]⟩
  have hO : IntervalIntegrable (sourceActionDensity s chi amp J K w) volume (1/2:ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1/2:ℝ)≤1)).mpr
      (sourceActionDensity_outer_integrable s chi amp J K w hs)
  have heq := intervalIntegral.integral_add_adjacent_intervals hI hO
  rw [intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤1),integral_Ioc_eq_integral_Ioo] at heq
  dsimp only [sourceDerivativeCutoff,sourceDerivativeHorizonCutoff,sourceDerivativeOuterIntegral]
  rw [← heq]
  dsimp only [sourceActionDensity]
  ring

theorem sourceDerivativeCutoff_tendsto (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) (hs : w-2*s≠0) :
    Tendsto (sourceDerivativeCutoff s chi amp J K w) (𝓝[>] (0:ℝ))
      (𝓝 (sourceDerivativeFinitePart s chi amp J K w)) := by
  have h := (sourceDerivativeHorizonCutoff_tendsto s chi amp J K w hw hwr hs).add_const
    (sourceDerivativeOuterIntegral s chi amp J K w)
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with e he
  exact (sourceDerivativeCutoff_eq s chi amp J K w hs he.1 he.2.le).symm

/-- The original incoming primitive vanishes in the unregularized source chamber. -/
theorem sourceActionIncomingPrimitive_tendsto_zero (s chi amp J K w : ℂ) (hwr : -1<w.re) :
    Tendsto (sourceActionIncomingPrimitive s chi amp J K w) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hr : 0<(w+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hp : Tendsto (fun z : ℝ => power (w+1) z) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh : Tendsto (fun z : ℝ => z^(w+1).re) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)^(w+1).re)) :=
      (Real.continuousAt_rpow_const (0:ℝ) (w+1).re (Or.inr hr.le)).tendsto.mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hr.ne'] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (Complex.norm_cpow_eq_rpow_re_of_pos hz (w+1)).symm
  have hpl : Tendsto (fun z : ℝ => power (w+1) z*(Real.log z:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := (tendsto_log_mul_rpow_nhdsGT_zero hr).norm
    simp only [norm_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [show ‖power (w+1) z‖=z^(w+1).re from Complex.norm_cpow_eq_rpow_re_of_pos hz (w+1),
      abs_of_nonneg (Real.rpow_nonneg hz.le _)]
    ring
  let A := sourceReaderIncomingCoefficient w chi*sourceRemainder s w amp J K 1 0
  let T := continuedOnset s w
  let D := deriv (continuedOnset s) w
  let B := -(Real.log 2:ℂ)*T/(w+1)-T/(2*(w+1)^2)+D/(w+1)
  have hh := ((hpl.mul_const (T/(2*(w+1)))).add (hp.mul_const B)).const_mul A
  simp only [zero_mul,zero_add,mul_zero] at hh
  apply hh.congr
  intro z
  dsimp only [sourceActionIncomingPrimitive,A,T,D,B]
  have hw1 : w+1≠0 := ne_of_apply_ne Complex.re hr.ne'
  field_simp [hw1]
  ring

/-- In the genuine chamber the full continuation equals the admitted
 unregularized source integral, so its normalization is fixed by the source. -/
theorem sourceDerivativeFinitePart_eq_integral (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) (hs : w-2*s≠0) :
    sourceDerivativeFinitePart s chi amp J K w=
      ∫ z in (0:ℝ)..1,sourceActionDensity s chi amp J K w z := by
  have hI := (sourceDifference_integral_tendsto s chi amp J K w hw hwr hs).1
  have hIcc : IntegrableOn (sourceActionDensity s chi amp J K w) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1),integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp hI
  have hc := (intervalIntegral.continuousOn_primitive_interval_left hIcc) (0:ℝ) left_mem_uIcc
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hc
  have hh := hc.mono (show Ioo (0:ℝ) 1⊆Icc (0:ℝ) 1 from Ioo_subset_Icc_self)
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0:ℝ)<1)] at hh
  have hlim := hh.add (sourceActionIncomingPrimitive_tendsto_zero s chi amp J K w (by linarith))
  simp only [add_zero] at hlim
  exact tendsto_nhds_unique (sourceDerivativeCutoff_tendsto s chi amp J K w hw (by linarith) hs) hlim

end
end RHTower.D4BMOriginalSourceResolvent
