import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedCutoffMajorant

/-! Spatial regularity and genuine L² admission of the analytic numerator, including at original poles. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology Metric MeasureTheory GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The undivided horizon moment has its actual endpoint derivative throughout the continued strip. -/
theorem horizonFirstMoment_hasDerivAt (s chi a J K w : ℂ) (hw : w.im ≠ 0) (hwre : -2 < w.re)
    {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (fun r => firstEndpointMellin (horizonMellinCore s chi a J K) r w)
      ((b:ℂ)^w*horizonMellinCore s chi a J K w b) b := by
  obtain ⟨R,C,hR,-,-,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw hb.1 hb.2
  have hw1 : w+1 ≠ 0 := by intro he; apply hw; have hi := congrArg Complex.im he; simpa using hi
  have hc : ContinuousAt (horizonMellinCore s chi a J K w) b :=
    ((gaussFactor_derivatives_continued (w := w) (chi := chi) false
      (enorm_ofReal_lt_one hb.1 hb.2)).1.comp_ofReal.continuousAt).mul
        (sourceRemainder_continuous s w a J K 1).continuousAt
  exact firstEndpointMellin_hasDerivAt hb.1 hwre hw1 (horizonMellinCore_measurable s chi a J K w) hc
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)

private theorem undividedOuterSource_continuousAt (s chi a J K w : ℂ)
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

/-- The undivided true outer-endpoint integral has its actual moving-endpoint derivative at every frequency. -/
theorem outerSourceIntegral_hasDerivAt (s chi a J K w : ℂ) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (fun r => ∫ t in Ioc r (1:ℝ), normalizable w chi t*sourceProfile s w a J K 1 t)
      (-(normalizable w chi b*sourceProfile s w a J K 1 b)) b := by
  let g : ℝ → ℂ := fun t => normalizable w chi t*sourceProfile s w a J K 1 t
  have hc : ContinuousOn g (Icc b 1) := fun t ht =>
    (undividedOuterSource_continuousAt s chi a J K w (hb.1.trans_le ht.1) ht.2).continuousWithinAt
  have hi : IntervalIntegrable g volume b 1 := hc.intervalIntegrable_of_Icc hb.2.le
  have hloc : ContinuousOn g (Ioo 0 1) := fun t ht =>
    (undividedOuterSource_continuousAt s chi a J K w ht.1 ht.2.le).continuousWithinAt
  have h := intervalIntegral.integral_hasDerivAt_left hi
    (hloc.stronglyMeasurableAtFilter isOpen_Ioo b hb)
    (undividedOuterSource_continuousAt s chi a J K w hb.1 hb.2.le)
  apply h.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hb.2] with t ht
  exact (intervalIntegral.integral_of_le ht.le).symm

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual undivided principal numerator is spatially continuous even at connection zeros. -/
theorem clearedPrincipalDifference_continuousAt (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (i : Fin 3) (t : ℝ) (ht : t < 0) :
    ContinuousAt (clearedPrincipalDifference q branch w a i) t := by
  let s := physicalRate q branch
  let chi := principalFrequency q i
  let J := principalAmplitude q i
  let K := principalGradient q branch i
  have hb := horizonCoordinate_interior t ht
  have hM := (horizonFirstMoment_hasDerivAt s chi a J K w hw hwre hb).continuousAt
  have hO := (outerSourceIntegral_hasDerivAt s chi a J K w hb).continuousAt
  have hN := (normalizable_derivatives_continued (w := w) (chi := chi) hb).1.continuousAt
  have hH := (horizon_derivatives_continued (w := w) (chi := chi) hb).1.continuousAt
  have h := ((hN.mul hM).add (hH.mul hO)).comp_of_eq (horizonCoordinate_hasDerivAt t).continuousAt rfl
  exact (h.mul continuousAt_const).add
    ((continuousAt_const.mul (radialLift_hasDerivAt s w a (clearedOnset s w) t).continuousAt).mul continuousAt_const)

/-- The analytic numerator itself, rather than a totalized quotient at a pole, is genuinely square-integrable. -/
theorem clearedCutoffRadialCoefficient_memLp (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwre : -2 < w.re) (hwr : |w.re| < 2) (i : Fin 3) :
    MemLp (clearedCutoffRadialCoefficient q branch w a i) 2 radialMeasure := by
  obtain ⟨R,b,C,hR,hb,hC,hM,hbound⟩ := clearedCutoffRadialCoefficient_local_bound q branch w a hw hwre hwr i
  have hc : ContinuousOn (clearedCutoffRadialCoefficient q branch w a i) (Iio 0) := by
    intro t ht
    exact (((horizonCoordinate_hasDerivAt t).ofReal_comp).continuousAt.mul
      (clearedPrincipalDifference_continuousAt q branch w a hw hwre i t ht)).continuousWithinAt
  apply MemLp.of_le hM (hc.aestronglyMeasurable measurableSet_Iio)
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  exact (hbound w (mem_ball_self hR) t ht).trans (le_abs_self _)

end
end RHTower.D4BMJointSource
