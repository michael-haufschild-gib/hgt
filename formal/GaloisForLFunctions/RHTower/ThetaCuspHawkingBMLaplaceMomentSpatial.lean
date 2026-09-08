import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSpatialODE
import GaloisForLFunctions.HTGeometry.FirstEndpointMellinSpatial
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceFundamentalContinuation

/-! Spatial derivatives of the actual continued endpoint moments, with their original source. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric MeasureTheory GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The literal continued source is continuous at every positive radius, for arbitrary frequency. -/
theorem continuedSourceProfile_continuousAt (s a J K w : ℂ) {b : ℝ} (hb : 0 < b) :
    ContinuousAt (continuedSourceProfile s a J K w) b :=
  (power_derivatives (w/2) hb).1.continuousAt.mul (sourceRemainder_continuous _ _ _ _ _ _).continuousAt

private theorem core_continuousAt (s chi a J K w : ℂ) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    ContinuousAt (horizonMellinCore s chi a J K w) b := by
  have hg := (gaussFactor_derivatives_continued (w := w) (chi := chi) false
    (enorm_ofReal_lt_one hb.1 hb.2)).1.comp_ofReal.continuousAt
  exact hg.mul (sourceRemainder_continuous s w a J K 1).continuousAt

/-- The original horizon source is precisely the Mellin integrand with the fixed onset restored. -/
theorem horizon_continuedSource_eq_mellin (s chi a J K w : ℂ) {t : ℝ} (ht : 0 < t) :
    horizon w chi t*continuedSourceProfile s a J K w t =
      (t:ℂ)^w*horizonMellinCore s chi a J K w t*(1/(w-2*s)+onsetCorrection (2*s) w) := by
  have hr (T : ℂ) : sourceRemainder s w a J K T t = sourceRemainder s w a J K 1 t*T := by
    unfold sourceRemainder
    ring
  have hp : power (w/2) t*power (w/2) t = (t:ℂ)^w := by
    rw [power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))]
    congr 1
    ring
  unfold horizon dress continuedSourceProfile sourceProfile horizonMellinCore
  rw [hr]
  calc
    _ = (power (w/2) t*power (w/2) t)*
        (gaussFactor w chi false (t:ℂ)*sourceRemainder s w a J K 1 t)*
          (1/(w-2*s)+onsetCorrection (2*s) w) := by ring
    _ = _ := by rw [hp]

/-- The subtracted horizon moment has the original normalized source as its actual spatial derivative. -/
theorem continuedHorizonMoment_hasDerivAt (s chi a J K w : ℂ) (hw : w.im ≠ 0)
    (hwre : -2 < w.re) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (fun t => continuedHorizonMoment s chi a J K t w)
      (horizon w chi b*continuedSourceProfile s a J K w b/(-connection w chi)) b := by
  obtain ⟨R,C,hR,-,-,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw hb.1 hb.2
  have hw1 : w+1 ≠ 0 := by intro he; apply hw; have hi := congrArg Complex.im he; simpa using hi
  have h := firstEndpointMellin_hasDerivAt hb.1 hwre hw1
    (horizonMellinCore_measurable s chi a J K w) (core_continuousAt s chi a J K w hb)
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)
  simpa only [horizon_continuedSource_eq_mellin s chi a J K w hb.1] using!
    (h.mul_const (1/(w-2*s)+onsetCorrection (2*s) w)).div_const (-connection w chi)

private theorem outer_source_continuousAt (s chi a J K w : ℂ)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ContinuousAt (fun t => normalizable w chi t*sourceProfile s w a J K 1 t) b := by
  have hn : ‖((1-b:ℝ):ℂ)‖ₑ < 1 := by
    rw [← ofReal_norm,ENNReal.ofReal_lt_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hb1)]
    linarith
  have hg := (gaussFactor_derivatives_continued (w := w) (chi := chi) true hn).1.comp_ofReal.continuousAt
  have hg' := hg.comp (show ContinuousAt (fun t : ℝ => 1-t) b by fun_prop)
  have hp := (power_derivatives (w/2) hb).1.continuousAt
  have ho : ContinuousAt (fun t : ℝ => power (1/2) (1-t)) b :=
    ((Complex.continuous_ofReal_cpow_const (y := (1/2:ℂ)) (by norm_num)).comp
      (show Continuous (fun t : ℝ => 1-t) by fun_prop)).continuousAt
  simpa only [normalizable,dress,outerFactor,sourceProfile,Function.comp_def,
    Complex.ofReal_sub,Complex.ofReal_one,Pi.mul_def,mul_assoc] using!
      ((hp.mul ho).mul hg').mul (hp.mul (sourceRemainder_continuous s w a J K 1).continuousAt)

/-- The true outer endpoint moment has its original moving-endpoint derivative at every frequency. -/
theorem continuedOuterMoment_hasDerivAt (s chi a J K w : ℂ) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (fun t => continuedOuterMoment s chi a J K t w)
      (-(normalizable w chi b*continuedSourceProfile s a J K w b/(-connection w chi))) b := by
  let g : ℝ → ℂ := fun t => normalizable w chi t*sourceProfile s w a J K 1 t
  have hc : ContinuousOn g (Icc b 1) := fun t ht =>
    (outer_source_continuousAt s chi a J K w (hb.1.trans_le ht.1) ht.2).continuousWithinAt
  have hi : IntervalIntegrable g volume b 1 := hc.intervalIntegrable_of_Icc hb.2.le
  have hloc : ContinuousOn g (Ioo 0 1) := fun t ht =>
    (outer_source_continuousAt s chi a J K w ht.1 ht.2.le).continuousWithinAt
  have h := intervalIntegral.integral_hasDerivAt_left hi
    (hloc.stronglyMeasurableAtFilter isOpen_Ioo b hb)
    (outer_source_continuousAt s chi a J K w hb.1 hb.2.le)
  have h' : HasDerivAt (fun t => ∫ u in Ioc t (1:ℝ), g u) (-g b) b := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hb.2] with t ht
    exact (intervalIntegral.integral_of_le ht.le).symm
  convert! (h'.mul_const (1/(w-2*s)+onsetCorrection (2*s) w)).div_const (-connection w chi) using 1
  dsimp [g,continuedSourceProfile,sourceProfile,sourceRemainder]
  ring

end
end RHTower.D4BMLaplaceRadial
