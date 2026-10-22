/-
Elementary source evaluation of the complete canonical QNM cutoff.
The actual forcing value, forcing slope and differentiated-source primitive
are evaluated without changing the original endpoint normalization.
-/

import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCanonicalSourceAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalMomentPolynomial
import Mathlib.Analysis.Calculus.Deriv.Slope

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource GaloisForLFunctions.HTGeometry
open D4BMOriginalMetricHorizon D4BMOriginalCanonicalHorizon
open D4BMOriginalCanonicalAction
noncomputable section
set_option autoImplicit false

/-- Exact first radial coefficient of the elementary fundamental source. -/
def fundamentalSourceCoreSlope (w s amp : ℂ) : ℂ :=
  -(2:ℂ)^(2*s-w)*amp^(2 : ℕ)*((2*s-w+2)/4*
    (fundamentalMomentConstant s+fundamentalMomentQuadratic w s)+fundamentalMomentQuadratic w s)

theorem fundamentalSourceCore_hasDerivAt_zero (w s amp : ℂ) :
    HasDerivAt (fundamentalSourceCore w s amp) (fundamentalSourceCoreSlope w s amp) 0 := by
  have hr := (Real.hasDerivAt_sqrt (by norm_num : (1:ℝ)-0≠0)).comp 0
    ((hasDerivAt_id (0:ℝ)).const_sub 1)
  have hp := (power_derivatives (2*s-w) (by norm_num : (0:ℝ)<1+Real.sqrt (1-0))).1.scomp 0
    (hr.const_add 1)
  have hhalf := (power_derivatives (1/2) (by norm_num : (0:ℝ)<1-0)).1.scomp 0
    ((hasDerivAt_id (0:ℝ)).const_sub 1)
  let A := (5*s^(2 : ℕ)+15*s+4)/4
  let B := s*(s-1)/4*((s+2)^(2 : ℕ)-((w+1)*(w+2)/2-(s+1)*(s+2)))
  have hpoly := ((((hasDerivAt_id (0:ℝ)).ofReal_comp).const_sub (1:ℂ)).mul_const B).const_add A
  have he : fundamentalSourceCore w s amp=fun z =>
      power (1/2) (1-z)*(power (2*s-w) (1+Real.sqrt (1-z))*amp^(2 : ℕ)*(A+(1-(z:ℂ))*B)) := by
    funext z
    dsimp only [fundamentalSourceCore,sourceRemainder,A,B]
    ring
  rw [he]
  apply ((hhalf.mul ((hp.mul_const (amp^(2 : ℕ))).mul hpoly))).congr_deriv
  norm_num only [Function.comp_def,Pi.mul_apply,id_eq,Complex.ofReal_zero,powerFirst,power,sub_zero,Real.sqrt_one,one_mul,one_div,Complex.ofReal_one,
    Complex.one_cpow,div_one,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,
    Complex.ofReal_ofNat,Complex.ofReal_mul,Complex.ofReal_add]
  dsimp only [A,B,fundamentalSourceCoreSlope,fundamentalMomentConstant,fundamentalMomentQuadratic]
  ring

private theorem physical_fundamental_root (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
    physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

/-- Original incoming forcing profile becomes exactly the elementary source,
 including its positive-radius horizon normalization. -/
theorem incomingProfile_QNM_eq_core (q : XiZeroCopy) (br side : Bool) (amp : ℂ)
    {z : ℝ} (hz : z∈Ico (0:ℝ) 1) :
    incomingProfile q br amp (D4BMOriginalCanonicalMetricCutoff.gradient q br)
      (physicalFundamentalFrequency q side) z=
      fundamentalSourceCore (physicalFundamentalFrequency q side) (physicalRate q br) amp z := by
  have hf := physical_fundamental_root q side
  have hw := (physicalFundamentalFrequency_strip q side).1
  dsimp only [incomingProfile,incomingCoefficient,gaussProfile,remainderProfile,D4BMOriginalCanonicalMetricCutoff.gradient]
  rw [fundamental_horizonRegularCoefficient _ _ hw hf,one_mul,
    gaussFactor_horizon_fundamental _ _ hw hf hz,reducedGreenGradient_fundamental _ _ _ hf]
  rfl

/-- The canonical forcing subtractions at a physical QNM are the actual
 elementary core's value and explicit slope; the opposite logarithmic term is zero. -/
theorem forcingCounterterms_QNM_evaluated (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    let K := D4BMOriginalCanonicalMetricCutoff.gradient q br
    incomingValue q br amp K w=fundamentalSourceCore w s amp 0 ∧
    incomingSlope q br amp K w=fundamentalSourceCoreSlope w s amp ∧
    oppositeValue q br amp K w=0 := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let K := D4BMOriginalCanonicalMetricCutoff.gradient q br
  have hf : incomingProfile q br amp K w =ᶠ[𝓝[>] (0:ℝ)] fundamentalSourceCore w s amp := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
    exact incomingProfile_QNM_eq_core q br side amp ⟨hz.1.le,hz.2⟩
  have hd := fundamentalSourceCore_hasDerivAt_zero w s amp
  have hv : incomingValue q br amp K w=fundamentalSourceCore w s amp 0 := by
    exact ((hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hf.symm).limUnder_eq
  refine ⟨hv,?_,?_⟩
  · change endpointJetSlope (incomingProfile q br amp K) w=_
    unfold endpointJetSlope
    change limUnder (𝓝[>] (0:ℝ)) (fun z => (incomingProfile q br amp K w z-incomingValue q br amp K w)/(z:ℂ))=_
    rw [hv]
    apply Filter.Tendsto.limUnder_eq
    have ht := hd.tendsto_slope_zero_right
    apply ht.congr'
    filter_upwards [hf] with z hz
    simp only [zero_add,Complex.real_smul,Complex.ofReal_inv]
    rw [hz]
    ring
  · change limUnder (𝓝[>] (0:ℝ)) (oppositeProfile q br amp K w)=0
    have he : oppositeProfile q br amp K w=fun _ => 0 := by
      funext z
      simp only [oppositeProfile,oppositeCoefficient,w,physicalFundamentalFrequency_connection_zero,
        zero_div,zero_mul]
    rw [he]
    exact (tendsto_const_nhds (x:=(0:ℂ))).limUnder_eq

/-- One elementary source integral with every original QNM counterterm
 evaluated. The onset and its derivative keep the physical source rate fixed. -/
def elementaryQNMActionCutoff (q : XiZeroCopy) (br side : Bool) (amp : ℂ) (e : ℝ) : ℂ :=
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let mu := physicalAngularParameter q^(2 : ℕ)-1/4
  let T := continuedOnset s w
  let Td := deriv (continuedOnset s) w
  let F := fundamentalSourceCore w s amp
  let F1 := fundamentalSourceCoreSlope w s amp;
  -mu*physicalSelfSourceCoefficient q*((∫ z in e..(1:ℝ),
    (z:ℂ)^w*F z*((mu-2)*((tortoiseOf z:ℂ)*T+Td)+w*T/(z:ℂ)))+
    (mu-2)*F 0*(e:ℂ)^(w+1)*
      ((((Real.log e:ℂ)/2-(Real.log 2:ℂ))*T)/(w+1)-T/(2*(w+1)^(2 : ℕ))+Td/(w+1))+
    w*T*(F 0*(e:ℂ)^w/w+F1*(e:ℂ)^(w+1)/(w+1)))

/-- The complete canonical QNM value is selected by this single elementary
 source cutoff, with no unevaluated Green response or boundary-transfer coefficient. -/
theorem elementaryQNMActionCutoff_tendsto (q : XiZeroCopy) (br side : Bool) (amp : ℂ) :
    Tendsto (elementaryQNMActionCutoff q br side amp) (𝓝[>] (0:ℝ))
      (𝓝 (canonicalQNMValue q br side amp)) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let chi := physicalRadialFrequency q
  let K := D4BMOriginalCanonicalMetricCutoff.gradient q br
  let mu := physicalAngularParameter q^(2 : ℕ)-1/4
  let C := physicalSelfSourceCoefficient q
  let T := continuedOnset s w
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q br side
  have hD := sourceDerivativeCutoff_tendsto s chi amp 1 K w hw.1 (abs_lt.mp hw.2).1 hs
  have hN := nativeForcingSourceCutoff_tendsto q br amp K w hw.1 (abs_lt.mp hw.2).1
  have ht := (hD.const_mul (-mu*(mu-2)*C)).add (hN.const_mul (mu*w*C*T))
  have hc := canonicalQNMValue_eq_source_finiteParts q br side amp
  change canonicalQNMValue q br side amp =
    -mu*(mu-2)*C*sourceDerivativeFinitePart s chi amp 1 K w+
      mu*w*C*T*nativeForcingSourceFinitePart q br amp K w at hc
  rw [← hc] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with e he
  have he1 : e<1 := by linarith [he.2]
  have hI : IntervalIntegrable (sourceActionDensity s chi amp 1 K w) volume e (1/2:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    apply (sourceActionDensity_continuousOn s chi amp 1 K w hs).mono
    rw [uIcc_of_le he.2.le]
    exact fun z hz => ⟨he.1.trans_le hz.1,by linarith [hz.2]⟩
  have hO : IntervalIntegrable (sourceActionDensity s chi amp 1 K w) volume (1/2:ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1/2:ℝ)≤1)).mpr
      (sourceActionDensity_outer_integrable s chi amp 1 K w hs)
  have hDF := hI.trans hO
  have hF : IntervalIntegrable (pullback q br amp K w) volume e 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le he1.le).mpr
      (nativeForcing_outer_integrable q br amp K w he.1 he1)
  have hsum : (∫ z in e..(1:ℝ),(z:ℂ)^w*fundamentalSourceCore w s amp z*
      ((mu-2)*((tortoiseOf z:ℂ)*T+deriv (continuedOnset s) w)+w*T/(z:ℂ)))=
      (mu-2)*(∫ z in e..1,sourceActionDensity s chi amp 1 K w z)-
        w*T*(∫ z in e..1,pullback q br amp K w z) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hDF.const_mul _) (hF.const_mul _)]
    apply intervalIntegral.integral_congr_uIoo
    intro z hz
    rw [uIoo_of_le he1.le] at hz
    have hz' : z∈Ioo (0:ℝ) 1 := ⟨he.1.trans hz.1,hz.2⟩
    have hp := physicalQNM_sourceAction_density q br side amp hz'
    have hn := nativeForcing_pullback_eq_source q br amp K w hz'
    dsimp only [sourceActionDensity]
    change _ = _
    dsimp only [w,s,chi,K,mu,T,D4BMOriginalCanonicalMetricCutoff.gradient] at ⊢ hn
    dsimp only at hp
    linear_combination -hp+(physicalFundamentalFrequency q side)*hn
  have hprim : sourceActionIncomingPrimitive s chi amp 1 K w e=
      fundamentalSourceCore w s amp 0*(e:ℂ)^(w+1)*
      ((((Real.log e:ℂ)/2-(Real.log 2:ℂ))*T)/(w+1)-T/(2*(w+1)^(2 : ℕ))+
        deriv (continuedOnset s) w/(w+1)) := by
    have hf := physical_fundamental_root q side
    have hR : sourceRemainder s w amp 1 K 1 0=fundamentalSourceCore w s amp 0 := by
      dsimp only [K,D4BMOriginalCanonicalMetricCutoff.gradient]
      rw [reducedGreenGradient_fundamental _ _ _ hf]
      simp only [fundamentalSourceCore,power,sub_zero,Complex.ofReal_one,Complex.one_cpow,one_mul]
      rfl
    dsimp only [sourceActionIncomingPrimitive,sourceReaderIncomingCoefficient]
    rw [fundamental_horizonRegularCoefficient _ _ hw.1 hf,one_mul,hR]
    rfl
  have hj := forcingCounterterms_QNM_evaluated q br side amp
  change incomingValue q br amp K w=fundamentalSourceCore w s amp 0 ∧
    incomingSlope q br amp K w=fundamentalSourceCoreSlope w s amp ∧oppositeValue q br amp K w=0 at hj
  dsimp only [sourceDerivativeCutoff,nativeForcingSourceCutoff]
  rw [hprim,hj.1,hj.2.1,hj.2.2,zero_mul,sub_zero]
  dsimp only [elementaryQNMActionCutoff]
  change _= -mu*C*((∫ z in e..(1:ℝ),(z:ℂ)^w*fundamentalSourceCore w s amp z*
      ((mu-2)*((tortoiseOf z:ℂ)*T+deriv (continuedOnset s) w)+w*T/(z:ℂ)))+_+_)
  rw [hsum]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
