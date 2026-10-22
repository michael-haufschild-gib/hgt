import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalSourceMoment
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-! Absolute admission and the full-endpoint finite part of the elementary fundamental source. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The elementary source core is continuous across both endpoints. -/
theorem fundamentalSourceCore_continuous (w s a : ℂ) : Continuous (fundamentalSourceCore w s a) := by
  have hp : Continuous (fun z : ℝ => power (1/2) (1-z)) :=
    (Complex.continuous_ofReal_cpow_const (y := (1/2:ℂ)) (by norm_num)).comp
      (show Continuous (fun z : ℝ => 1-z) by fun_prop)
  exact hp.mul (sourceRemainder_continuous s w a 1 ((w+1)*(w+2)/2-(s+1)*(s+2)) 1)

/-- The elementary density is absolutely integrable on every interval away from the horizon. -/
theorem fundamentalSourceDensity_intervalIntegrable (w s a : ℂ) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    IntervalIntegrable (fun z : ℝ => (z:ℂ)^w*fundamentalSourceCore w s a z) volume b 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc hb1
  intro z hz
  exact ((power_derivatives w (hb.trans_le hz.1)).1.continuousAt.mul
    (fundamentalSourceCore_continuous w s a).continuousAt).continuousWithinAt

/-- The first endpoint subtraction makes the actual fundamental source absolutely integrable. -/
theorem fundamentalSourceRemainder_intervalIntegrable (w chi s a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) :
    IntervalIntegrable (fun z : ℝ => (z:ℂ)^w*(fundamentalSourceCore w s a z-fundamentalSourceCore w s a 0))
      volume 0 1 := by
  let F := horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)
  obtain ⟨R,C,hR,-,-,hC⟩ := horizonMellinCore_uniform_first_bound s chi a 1
    (reducedGreenGradient chi s 1) w hw (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hi := firstEndpointMellinRemainder_integrable (F := F) (by norm_num : (0:ℝ)≤1/2) hwr
    (horizonMellinCore_measurable s chi a 1 (reducedGreenGradient chi s 1) w)
    (fun z hz => hC w (mem_ball_self hR) z ⟨hz.1.le,hz.2⟩)
  have he : IntegrableOn (fun z : ℝ => (z:ℂ)^w*
      (fundamentalSourceCore w s a z-fundamentalSourceCore w s a 0)) (Ioc 0 (1/2:ℝ)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    dsimp only [F]
    rw [horizonMellinCore_fundamental w chi s a hw hf ⟨hz.1.le,by linarith [hz.2]⟩,
      horizonMellinCore_fundamental w chi s a hw hf (by simp : (0:ℝ) ∈ Ico 0 1)]
  have hfirst := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1/2)).mpr he
  have hlast : IntervalIntegrable (fun z : ℝ => (z:ℂ)^w*
      (fundamentalSourceCore w s a z-fundamentalSourceCore w s a 0)) volume (1/2) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (1/2:ℝ)≤1)
    intro z hz
    exact ((power_derivatives w (by linarith [hz.1])).1.continuousAt.mul
      ((fundamentalSourceCore_continuous w s a).continuousAt.sub continuousAt_const)).continuousWithinAt
  exact hfirst.trans hlast

/-- Both literal pieces join into the unique full-endpoint first-subtracted Mellin integral. -/
theorem fundamentalSourceMoment_eq_full_endpoint (w chi s a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) :
    fundamentalSourceMoment w s a=
      firstEndpointMellin (fun u => fundamentalSourceCore u s a) 1 w := by
  let F := fundamentalSourceCore w s a
  let P : ℝ → ℂ := fun z => (z:ℂ)^w
  let R : ℝ → ℂ := fun z => P z*(F z-F 0)
  have hR : IntervalIntegrable R volume 0 1 :=
    fundamentalSourceRemainder_intervalIntegrable w chi s a hw hwr hf
  have hP : IntervalIntegrable P volume (1/2) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (1/2:ℝ)≤1)
    intro z hz
    exact (power_derivatives w (by linarith [hz.1])).1.continuousAt.continuousWithinAt
  have hD := fundamentalSourceDensity_intervalIntegrable w s a (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)≤1)
  have h0h : IntervalIntegrable R volume 0 (1/2) := hR.mono_set (by
    norm_num [uIcc]
    intro z hz
    constructor <;> linarith [hz.1,hz.2])
  have hh1 : IntervalIntegrable R volume (1/2) 1 := hR.mono_set (by
    norm_num [uIcc]
    intro z hz
    constructor <;> linarith [hz.1,hz.2])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0h hh1
  have htail : (∫ z in (1/2:ℝ)..1, R z)=
      (∫ z in (1/2:ℝ)..1, P z*F z)-(∫ z in (1/2:ℝ)..1, P z)*F 0 := by
    simp only [R,mul_sub]
    rw [intervalIntegral.integral_sub hD (hP.mul_const _),intervalIntegral.integral_mul_const]
  have hw1 : w ≠ -1 := by intro he; apply hw; simp [he]
  have hpower : (∫ z in (1/2:ℝ)..1, P z)=(1-(1/2:ℂ)^(w+1))/(w+1) := by
    rw [integral_cpow (Or.inr ⟨hw1,by norm_num [uIcc]⟩)]
    simp
  rw [htail,hpower] at hsplit
  dsimp only [fundamentalSourceMoment,firstEndpointMellin,firstEndpointMellinRemainder]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1/2),
    ← intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤1),
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  change F 0*((1/2:ℝ):ℂ)^(w+1)/(w+1)+(∫ z in (0:ℝ)..(1/2), R z)+
    (∫ z in (1/2:ℝ)..1, P z*F z)=F 0*(1:ℂ)^(w+1)/(w+1)+(∫ z in (0:ℝ)..1, R z)
  push_cast
  rw [Complex.one_cpow,hsplit.symm]
  ring

/-- Every actual Xi source has one absolutely admitted elementary full-endpoint finite part. -/
theorem physicalFundamentalSourceMoment_integral (q : XiZeroCopy) (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := D4BMModularCore.physicalRate q branch
    IntervalIntegrable (fun z : ℝ => (z:ℂ)^w*
      (fundamentalSourceCore w s a z-fundamentalSourceCore w s a 0)) volume 0 1 ∧
    fundamentalSourceMoment w s a=fundamentalSourceCore w s a 0/(w+1)+
      ∫ z in Ioc (0:ℝ) 1, (z:ℂ)^w*(fundamentalSourceCore w s a z-fundamentalSourceCore w s a 0) := by
  dsimp only
  have hw := physicalFundamentalFrequency_strip q side
  have hf : physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  refine ⟨fundamentalSourceRemainder_intervalIntegrable _ _ _ _ hw.1 (abs_lt.mp hw.2).1 hf,?_⟩
  rw [fundamentalSourceMoment_eq_full_endpoint _ _ _ _ hw.1 (abs_lt.mp hw.2).1 hf]
  simp only [firstEndpointMellin,firstEndpointMellinRemainder,Complex.ofReal_one,Complex.one_cpow,mul_one]

end
end RHTower.D4BMJointSource
