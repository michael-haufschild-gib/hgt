import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCanonicalSourcePeriodAttachment
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource D4BMOriginalCanonicalAction
  GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Every actual fundamental QNM is inside the original causal time chamber. -/
theorem physicalFundamentalFrequency_time_chamber (q : XiZeroCopy) (br side : Bool) :
    (2*physicalRate q br).re < (physicalFundamentalFrequency q side).re := by
  obtain ⟨ha,hb⟩ := xi_divisor_support_re_mem_open_unit q.1
  rw [physicalFundamentalFrequency_eq]
  cases br <;> cases side <;>
    norm_num [physicalRate,Complex.mul_re,Complex.div_re] <;> linarith

private theorem causalOnset_norm_le (v w : ℂ) (u : ℝ) :
    ‖(Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ))‖ ≤
      Real.exp ((v.re-w.re)*u) := by
  have hc : ‖(Real.smoothTransition u:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg u)] using Real.smoothTransition.le_one u
  rw [norm_mul,Complex.norm_exp]
  have he : ((v-w)*(u:ℂ)).re=(v.re-w.re)*u := by simp
  rw [he]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) hc

/-- Differentiating the original convergent onset retains minus the actual time. -/
theorem causalOnset_integrable_hasDerivAt (v w : ℂ) (hw : v.re<w.re) :
    IntegrableOn (fun u : ℝ => -(u:ℂ)*
      ((Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ)))) (Ioi 0) ∧
    HasDerivAt (onsetTransform v)
      (∫ u in Ioi (0:ℝ), -(u:ℂ)*
        ((Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ)))) w := by
  let d := (w.re-v.re)/2
  have hd : 0<d := by dsimp [d];linarith
  have hi : IntegrableOn (fun u : ℝ => u*Real.exp (-d*u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s:=1) (p:=1)
        (by norm_num) (by norm_num) hd)
  have hm : ∀ᶠ z : ℂ in 𝓝 w, AEStronglyMeasurable
      (fun u : ℝ => (Real.smoothTransition u:ℂ)*Complex.exp ((v-z)*(u:ℂ)))
      (volume.restrict (Ioi 0)) := by
    filter_upwards with z
    fun_prop
  have hm' : AEStronglyMeasurable
      (fun u : ℝ => -(u:ℂ)*((Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ))))
      (volume.restrict (Ioi 0)) := by fun_prop
  have hb : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (0:ℝ))), ∀ z ∈ Metric.ball w d,
      ‖-(u:ℂ)*((Real.smoothTransition u:ℂ)*Complex.exp ((v-z)*(u:ℂ)))‖ ≤
        u*Real.exp (-d*u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hdist : ‖z-w‖<d := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
    have hre := (Complex.abs_re_le_norm (z-w)).trans_lt hdist
    have hzre : v.re-z.re ≤ -d := by
      rw [Complex.sub_re,abs_lt] at hre
      dsimp [d] at *
      linarith [hre.1]
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.le]
    apply mul_le_mul_of_nonneg_left _ hu.le
    exact (causalOnset_norm_le v z u).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzre hu.le))
  have hderiv : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (0:ℝ))), ∀ z ∈ Metric.ball w d,
      HasDerivAt (fun z : ℂ => (Real.smoothTransition u:ℂ)*Complex.exp ((v-z)*(u:ℂ)))
        (-(u:ℂ)*((Real.smoothTransition u:ℂ)*Complex.exp ((v-z)*(u:ℂ)))) z := by
    filter_upwards with u z hz
    apply ((((hasDerivAt_id z).const_sub v).mul_const (u:ℂ)).cexp.const_mul
      (Real.smoothTransition u:ℂ)).congr_deriv
    simp only [id_eq]
    ring
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun z u => (Real.smoothTransition u:ℂ)*Complex.exp ((v-z)*(u:ℂ)))
    (F':=fun z u => -(u:ℂ)*((Real.smoothTransition u:ℂ)*Complex.exp ((v-z)*(u:ℂ))))
    (Metric.ball_mem_nhds w hd) hm (onsetTransform_integrable v w hw) hm' hb hi hderiv

/-- At actual QNMs, the continued onset and its derivative are ordinary time moments. -/
theorem physicalOnset_time_moments (q : XiZeroCopy) (br side : Bool) :
    let w := physicalFundamentalFrequency q side
    let s := physicalRate q br
    continuedOnset s w = onsetTransform (2*s) w ∧
      deriv (continuedOnset s) w =
        ∫ u in Ioi (0:ℝ), -(u:ℂ)*
          ((Real.smoothTransition u:ℂ)*Complex.exp ((2*s-w)*(u:ℂ))) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  have hw := physicalFundamentalFrequency_time_chamber q br side
  have he : continuedOnset s =ᶠ[𝓝 w] onsetTransform (2*s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
    exact (onsetTransform_eq (2*s) z hz).symm
  exact ⟨he.eq_of_nhds,((causalOnset_integrable_hasDerivAt (2*s) w hw).2.congr_of_eventuallyEq he).deriv⟩

/-- The source-retaining causal profile; its spatial finite-part attachment is proved below. -/
def canonicalCausalSourceProfile (q : XiZeroCopy) (br side : Bool) (a : ℂ) (u : ℝ) : ℂ :=
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let mu := physicalAngularParameter q^2-1/4;
  -mu*physicalSelfSourceCoefficient q*(Real.smoothTransition u:ℂ)*Complex.exp (2*s*(u:ℂ))*
    ((mu-2)*(fundamentalSourceTortoiseMoment w s a-(u:ℂ)*fundamentalSourceMoment w s a)+
      fundamentalSourceForcingMoment w s a)

/-- The original static-time source at a spatial cutoff, including its original
power, logarithmic and forcing counterterms. -/
def canonicalCausalSourceCutoff (q : XiZeroCopy) (br side : Bool) (a : ℂ) (u e : ℝ) : ℂ :=
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let mu := physicalAngularParameter q^2-1/4
  let F := fundamentalSourceCore w s a;
  -mu*physicalSelfSourceCoefficient q*(Real.smoothTransition u:ℂ)*Complex.exp (2*s*(u:ℂ))*
    ((∫ z in e..(1:ℝ), (z:ℂ)^w*F z*((mu-2)*((tortoiseOf z:ℂ)-(u:ℂ))+w/(z:ℂ)))+
      (mu-2)*F 0*(e:ℂ)^(w+1)*
        (((Real.log e:ℂ)/2-(Real.log 2:ℂ)-(u:ℂ))/(w+1)-1/(2*(w+1)^2))+
      F 0*(e:ℂ)^w+w*fundamentalSourceCoreSlope w s a*(e:ℂ)^(w+1)/(w+1))

/-- This receiver is selected by the original source cutoff, rather than chosen
to agree with the canonical value. The original finite constants are retained. -/
theorem canonicalCausalSourceCutoff_tendsto (q : XiZeroCopy) (br side : Bool) (a : ℂ) (u : ℝ) :
    Tendsto (fun e : ℝ => canonicalCausalSourceCutoff q br side a u (e*(2-e)))
      (𝓝[>] (0:ℝ)) (𝓝 (canonicalCausalSourceProfile q br side a u)) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let mu := physicalAngularParameter q^2-1/4
  let K := -mu*physicalSelfSourceCoefficient q*(Real.smoothTransition u:ℂ)*Complex.exp (2*s*(u:ℂ))
  have hstrip := physicalFundamentalFrequency_strip q side
  have hw : -2<w.re := (abs_lt.mp hstrip.2).1
  have hw1 : w+1≠0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hh
    exact hstrip.1 hh
  have hphi : Tendsto (fun e : ℝ => e*(2-e)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · have h : ContinuousAt (fun e : ℝ => e*(2-e)) 0 := by fun_prop
      simpa only [zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
      exact mul_pos he.1 (by linarith [he.2])
  have hM := (physicalFundamentalSourceMoment_cutoff q br side a).comp hphi
  have hX := fundamentalSourceTortoiseMoment_original_cutoff w s a hw hw1
  have hY := fundamentalSourceForcingMoment_original_cutoff w s a hw hw1
  have h := (((hX.sub (hM.const_mul (u:ℂ))).const_mul (mu-2)).add hY).const_mul K
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  let b := e*(2-e)
  have hb : 0<b := mul_pos he.1 (by linarith [he.2])
  have hb1 : b≤1 := by dsimp [b];nlinarith [sq_nonneg (1-e)]
  have hMInt := fundamentalSourceDensity_intervalIntegrable w s a hb hb1
  have hXInt : IntervalIntegrable
      (fun z : ℝ => (z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ)) volume b 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb1
    intro z hz
    have hz0 := hb.trans_le hz.1
    have hx : ContinuousAt tortoiseOf z := by
      unfold tortoiseOf
      fun_prop (disch := positivity)
    exact (((power_derivatives w hz0).1.continuousAt.mul
      (fundamentalSourceCore_continuous w s a).continuousAt).mul
        (Complex.continuous_ofReal.continuousAt.comp hx)).continuousWithinAt
  have hYInt : IntervalIntegrable
      (fun z : ℝ => (z:ℂ)^(w-1)*fundamentalSourceCore w s a z) volume b 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb1
    intro z hz
    exact ((power_derivatives (w-1) (hb.trans_le hz.1)).1.continuousAt.mul
      (fundamentalSourceCore_continuous w s a).continuousAt).continuousWithinAt
  have hsplit : (∫ z in b..1, (z:ℂ)^w*fundamentalSourceCore w s a z*
      ((mu-2)*((tortoiseOf z:ℂ)-(u:ℂ))+w/(z:ℂ)))=
      (mu-2)*((∫ z in b..1,(z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ))-
        (u:ℂ)*(∫ z in b..1,(z:ℂ)^w*fundamentalSourceCore w s a z))+
      w*(∫ z in b..1,(z:ℂ)^(w-1)*fundamentalSourceCore w s a z) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hXInt (hMInt.const_mul (u:ℂ)),
      ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((hXInt.sub (hMInt.const_mul (u:ℂ))).const_mul (mu-2)) (hYInt.const_mul w)]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hb1] at hz
    have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hb.trans_le hz.1).ne'
    dsimp only
    rw [Complex.cpow_sub _ _ hz0,Complex.cpow_one]
    ring
  change _ = canonicalCausalSourceCutoff q br side a u b
  dsimp only [canonicalCausalSourceCutoff]
  change _ = K*((∫ z in b..1, (z:ℂ)^w*fundamentalSourceCore w s a z*
    ((mu-2)*((tortoiseOf z:ℂ)-(u:ℂ))+w/(z:ℂ)))+
    (mu-2)*fundamentalSourceCore w s a 0*(b:ℂ)^(w+1)*
      (((Real.log b:ℂ)/2-(Real.log 2:ℂ)-(u:ℂ))/(w+1)-1/(2*(w+1)^2))+
    fundamentalSourceCore w s a 0*(b:ℂ)^w+
    w*fundamentalSourceCoreSlope w s a*(b:ℂ)^(w+1)/(w+1))
  rw [hsplit]
  dsimp only [Function.comp_apply,w,s,b] at hw1 ⊢
  field_simp [hw1]
  ring

/-- Full canonical temporal/metric/QNM matching to the source-derived causal
profile. The time integral is absolutely convergent at every actual QNM. -/
theorem canonicalCausalSourceProfile_laplace (q : XiZeroCopy) (br side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    IntegrableOn (fun u : ℝ => Complex.exp (-w*(u:ℂ))*canonicalCausalSourceProfile q br side a u)
      (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), Complex.exp (-w*(u:ℂ))*canonicalCausalSourceProfile q br side a u)=
      canonicalQNMValue q br side a := by
  dsimp only
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q br
  let mu := physicalAngularParameter q^2-1/4
  let K := -mu*physicalSelfSourceCoefficient q
  let M := fundamentalSourceMoment w s a
  let X := fundamentalSourceTortoiseMoment w s a
  let Y := fundamentalSourceForcingMoment w s a
  let F := fun u : ℝ => (Real.smoothTransition u:ℂ)*Complex.exp ((2*s-w)*(u:ℂ))
  let U := fun u : ℝ => -(u:ℂ)*F u
  have hw := physicalFundamentalFrequency_time_chamber q br side
  have hF : IntegrableOn F (Ioi 0) := onsetTransform_integrable (2*s) w hw
  have hU : IntegrableOn U (Ioi 0) := (causalOnset_integrable_hasDerivAt (2*s) w hw).1
  have he : (fun u : ℝ => Complex.exp (-w*(u:ℂ))*canonicalCausalSourceProfile q br side a u)=
      fun u => K*((mu-2)*(F u*X+U u*M)+F u*Y) := by
    funext u
    have hex : Complex.exp (-w*(u:ℂ))*Complex.exp (2*s*(u:ℂ))=
        Complex.exp ((2*s-w)*(u:ℂ)) := by rw [← Complex.exp_add];congr 1;ring
    change Complex.exp (-w*(u:ℂ))*
      (K*(Real.smoothTransition u:ℂ)*Complex.exp (2*s*(u:ℂ))*((mu-2)*(X-(u:ℂ)*M)+Y))=_
    calc
      _ = K*(Real.smoothTransition u:ℂ)*
          (Complex.exp (-w*(u:ℂ))*Complex.exp (2*s*(u:ℂ)))*((mu-2)*(X-(u:ℂ)*M)+Y) := by ring
      _ = _ := by rw [hex];dsimp only [F,U];ring
  rw [he]
  have hA : IntegrableOn (fun u => F u*X+U u*M) (Ioi 0) :=
    (hF.mul_const X).add (hU.mul_const M)
  have hB : IntegrableOn (fun u => (mu-2)*(F u*X+U u*M)) (Ioi 0) := hA.const_mul (mu-2)
  refine ⟨(hB.add (hF.mul_const Y)).const_mul K,?_⟩
  rw [integral_const_mul,
    integral_add hB (hF.mul_const Y),
    integral_const_mul,integral_add (hF.mul_const X) (hU.mul_const M),
    integral_mul_const,integral_mul_const,integral_mul_const]
  have hm := physicalOnset_time_moments q br side
  rw [canonicalQNMValue_eq_source_periods]
  dsimp only at hm ⊢
  rw [hm.1,hm.2]
  change K*((mu-2)*((∫ u in Ioi (0:ℝ),F u)*X+(∫ u in Ioi (0:ℝ),U u)*M)+
    (∫ u in Ioi (0:ℝ),F u)*Y)=
    K*((mu-2)*((∫ u in Ioi (0:ℝ),U u)*M+(∫ u in Ioi (0:ℝ),F u)*X)+
      (∫ u in Ioi (0:ℝ),F u)*Y)
  ring

end
end RHTower.D4BMOriginalSourceResolvent
