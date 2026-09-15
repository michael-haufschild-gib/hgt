import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalSourceLogTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalSourceForcingTransport

/-! Exact attachment of the complete canonical temporal/metric/QNM action to its source periods. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource D4BMOriginalCanonicalAction
  GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

private theorem originalSourceTortoise_intervalIntegrable (w s a : ℂ) {b : ℝ}
    (hb : 0<b) (hb1 : b≤1) :
    IntervalIntegrable (fun z : ℝ => (z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ)) volume b 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc hb1
  intro z hz
  have hz0 := hb.trans_le hz.1
  have hsz : 0<Real.sqrt z := Real.sqrt_pos.mpr hz0
  have hx : ContinuousAt tortoiseOf z := by
    unfold tortoiseOf
    fun_prop (disch := positivity)
  exact (((power_derivatives w hz0).1.continuousAt.mul
    (fundamentalSourceCore_continuous w s a).continuousAt).mul
      (Complex.continuous_ofReal.continuousAt.comp hx)).continuousWithinAt

/-- The complete canonical value, including the actual metric response,
fixed-source temporal derivative and twice-subtracted forcing, equals its
three original source periods. -/
theorem canonicalQNMValue_eq_source_periods (q : XiZeroCopy) (br side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    let mu := physicalAngularParameter q^2-1/4
    canonicalQNMValue q br side a = -mu*physicalSelfSourceCoefficient q*
      ((mu-2)*(deriv (continuedOnset s) w*fundamentalSourceMoment w s a+
        continuedOnset s w*fundamentalSourceTortoiseMoment w s a)+
          continuedOnset s w*fundamentalSourceForcingMoment w s a) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let mu := physicalAngularParameter q^2-1/4
  let T := continuedOnset s w
  let Td := deriv (continuedOnset s) w
  have hstrip := physicalFundamentalFrequency_strip q side
  have hw : -2<w.re := (abs_lt.mp hstrip.2).1
  have hw0 : w≠0 := by intro h;apply hstrip.1;change w.im=0;rw [h];rfl
  have hw1 : w+1≠0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hh
    exact hstrip.1 hh
  have hphi : Tendsto (fun x : ℝ=>x*(2-x)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · have h : ContinuousAt (fun x : ℝ=>x*(2-x)) 0 := by fun_prop
      simpa only [zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with x hx
      exact mul_pos hx.1 (by linarith [hx.2])
  have hc := (elementaryQNMActionCutoff_tendsto q br side a).comp hphi
  have hM := (physicalFundamentalSourceMoment_cutoff q br side a).comp hphi
  have hX := fundamentalSourceTortoiseMoment_original_cutoff w s a hw hw1
  have hY := fundamentalSourceForcingMoment_original_cutoff w s a hw hw1
  have h := ((((hM.const_mul Td).add (hX.const_mul T)).const_mul (mu-2)).add
    (hY.const_mul T)).const_mul (-mu*physicalSelfSourceCoefficient q)
  apply tendsto_nhds_unique hc
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  let b := e*(2-e)
  have hb : 0<b := mul_pos he.1 (by linarith [he.2])
  have hb1 : b≤1 := by dsimp [b];nlinarith [sq_nonneg (1-e)]
  have hMInt := fundamentalSourceDensity_intervalIntegrable w s a hb hb1
  have hXInt := originalSourceTortoise_intervalIntegrable w s a hb hb1
  -- The forcing source core keeps w; only its outer Mellin exponent shifts.
  have hYInt' : IntervalIntegrable (fun z : ℝ => (z:ℂ)^(w-1)*fundamentalSourceCore w s a z) volume b 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb1
    intro z hz
    exact ((power_derivatives (w-1) (hb.trans_le hz.1)).1.continuousAt.mul
      (fundamentalSourceCore_continuous w s a).continuousAt).continuousWithinAt
  have hsplit : (∫ z in b..1, (z:ℂ)^w*fundamentalSourceCore w s a z*
      ((mu-2)*((tortoiseOf z:ℂ)*T+Td)+w*T/(z:ℂ)))=
      (mu-2)*(Td*(∫ z in b..1,(z:ℂ)^w*fundamentalSourceCore w s a z)+
        T*(∫ z in b..1,(z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ)))+
      T*w*(∫ z in b..1,(z:ℂ)^(w-1)*fundamentalSourceCore w s a z) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hMInt.const_mul Td) (hXInt.const_mul T),
      ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (((hMInt.const_mul Td).add (hXInt.const_mul T)).const_mul (mu-2))
        (hYInt'.const_mul (T*w))]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hb1] at hz
    have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hb.trans_le hz.1).ne'
    dsimp only
    rw [Complex.cpow_sub _ _ hz0,Complex.cpow_one]
    ring
  change _ = elementaryQNMActionCutoff q br side a b
  dsimp only [elementaryQNMActionCutoff]
  change _ = -mu*physicalSelfSourceCoefficient q*((∫ z in b..1,
    (z:ℂ)^w*fundamentalSourceCore w s a z*((mu-2)*((tortoiseOf z:ℂ)*T+Td)+w*T/(z:ℂ)))+
    (mu-2)*fundamentalSourceCore w s a 0*(b:ℂ)^(w+1)*
      ((((Real.log b:ℂ)/2-(Real.log 2:ℂ))*T)/(w+1)-T/(2*(w+1)^2)+Td/(w+1))+
    w*T*(fundamentalSourceCore w s a 0*(b:ℂ)^w/w+
      fundamentalSourceCoreSlope w s a*(b:ℂ)^(w+1)/(w+1)))
  rw [hsplit]
  dsimp only [Function.comp_apply,w,s,b] at hw0 hw1 ⊢
  field_simp [hw0,hw1]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
