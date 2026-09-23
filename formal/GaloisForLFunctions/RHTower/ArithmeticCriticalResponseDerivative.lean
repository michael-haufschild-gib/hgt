import GaloisForLFunctions.RHTower.ArithmeticReflectionDiskAdmission
import GaloisForLFunctions.RHTower.ArithmeticLogarithmicSecondFlux
import GaloisForLFunctions.RHTower.ArithmeticUnitPhaseRigidity
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Critical arithmetic response and the normalized zeta derivative

The proved symmetric cubic source expansion identifies the critical logarithmic response
with the derivative of the same literal analytic source. Exact rational cancellation gives
`L_full(t) + V(1/2 + i*t) = conj (Z'(1/2 + i*t))`, where `Z(s)=zeta(s)/(s*(s+1))`.

The complete target varies by an explicit quadratic correction away from the critical line.
Both existing off-line-zero disks therefore constrain this actual normalized derivative.
The compensated second arithmetic current reconstructs the same derivative after all target
and boundary terms are retained. No independent lower bound or zero exclusion is asserted.
-/

set_option autoImplicit false
noncomputable section
open Complex Real MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- Critical point with the same height as the arithmetic response. -/
def criticalResponsePoint (t : ℝ) : ℂ := 1/2+(t:ℂ)*Complex.I

/-- The literal full Fourier source before conjugation. -/
def fullUnitHolomorphicSource (s : ℂ) : ℂ := unitPhaseSource s+1/(12*(s+1))

/-- Actual rational target from the complete reflected zero balance. -/
def reflectionZeroTarget (s : ℂ) : ℂ :=
  (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
    1/(12*(star s+1)*(2-s)))

/-- Symmetric source quotient, used only through its punctured critical limit. -/
def criticalResponseQuotient (t h : ℝ) : ℂ :=
  (unitFullFourierSource (criticalResponsePoint t+(h:ℂ))-
    unitFullFourierSource (criticalResponsePoint t-(h:ℂ)))/((2*h:ℝ):ℂ)

/-- The exact full source and its analytic expression agree throughout the strip. -/
theorem unitFullFourierSource_eq_star_holomorphic {s : ℂ} (hs : s ∈ minimumStrip) :
    unitFullFourierSource s=star (fullUnitHolomorphicSource s) := by
  rw [unitFullFourierSource_eq_remainder hs.1 (unitPhaseStrip_denominators hs).2.1,
    normalizedWeightedRemainder_one_eq_star_source hs]
  simp [fullUnitHolomorphicSource,mul_comm]

/-- The fixed zeta normalization is differentiable inside the strip. -/
theorem differentiableAt_normalizedMinimumZeta {s : ℂ} (hs : s ∈ minimumStrip) :
    DifferentiableAt ℂ normalizedMinimumZeta s := by
  have hd := unitPhaseStrip_denominators hs
  exact (unitPhaseZeta_analytic s hs).differentiableAt.div
    (differentiableAt_id.mul (differentiableAt_id.add_const (1:ℂ)))
    (mul_ne_zero hd.1 hd.2.2)

/-- Exact derivative of the complete analytic source, retaining both rational terms. -/
theorem hasDerivAt_fullUnitHolomorphicSource {s : ℂ} (hs : s ∈ minimumStrip) :
    HasDerivAt fullUnitHolomorphicSource
      ((1-2*s)/(2*(s*(1-s))^(2 : ℕ))-deriv normalizedMinimumZeta s-1/(12*(s+1)^(2 : ℕ))) s := by
  have hd := unitPhaseStrip_denominators hs
  have hmean := (hasDerivAt_const s (1:ℂ)).div
    (((hasDerivAt_id s).add_const (1:ℂ)).const_mul (12:ℂ))
    (mul_ne_zero (by norm_num) hd.2.2)
  convert! ((hasDerivAt_unitPhaseBoundary hs).sub
    (differentiableAt_normalizedMinimumZeta hs).hasDerivAt).add hmean using 1
  dsimp only [id_eq]
  field_simp
  ring

/-- Cubic source control gives the actual symmetric quotient a quadratic error. -/
theorem norm_criticalResponseQuotient_add_le (t : ℝ) {h : ℝ}
    (hh : |h|≤1/2) (hh0 : h≠0) :
    ‖criticalResponseQuotient t h+criticalFullLogResponse t‖ ≤ h^(2 : ℕ)/12 := by
  let s := criticalResponsePoint t+(h:ℂ)
  have hsre : s.re=1/2+h := by simp [s,criticalResponsePoint]
  have hsim : s.im=t := by simp [s,criticalResponsePoint]
  have hr : 1-star s=criticalResponsePoint t-(h:ℂ) := by
    apply Complex.ext
    · simp [s,criticalResponsePoint]; ring
    · simp [s,criticalResponsePoint]
  have hab := abs_le.mp hh
  have hd : s.re≠1/2 := by rw [hsre]; intro hz; apply hh0; linarith
  have he := norm_unitFullFourierSource_divided_reflection_response_le
    (s := s) (by rw [hsre]; linarith) (by rw [hsre]; linarith) hd
  rw [hr,hsre,hsim,show (1/2:ℝ)+h-1/2=h by ring] at he
  exact he

/-- The actual source expansion fixes its punctured critical quotient limit. -/
theorem tendsto_criticalResponseQuotient (t : ℝ) :
    Tendsto (criticalResponseQuotient t) (𝓝[≠] (0:ℝ)) (𝓝 (-criticalFullLogResponse t)) := by
  have hb : Tendsto (fun h : ℝ => h^(2 : ℕ)/12) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    simpa using (((continuous_id.pow 2).div_const (12:ℝ)).tendsto' (0:ℝ) 0 (by norm_num)).mono_left
      nhdsWithin_le_nhds
  have he : ∀ᶠ h : ℝ in 𝓝[≠] (0:ℝ), ‖criticalResponseQuotient t h+criticalFullLogResponse t‖ ≤ h^(2 : ℕ)/12 := by
    have hh : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), |h|<1/2 :=
      (continuous_abs.tendsto 0).eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hh hh0
    exact norm_criticalResponseQuotient_add_le t hh.le (by simpa using hh0)
  have h := (squeeze_zero_norm' he hb).sub_const (criticalFullLogResponse t)
  simpa only [add_sub_cancel_right,zero_sub] using h

/-- The same source quotient has the derivative of its literal analytic expression as limit. -/
theorem criticalFullLogResponse_eq_neg_star_source_derivative (t : ℝ) :
    criticalFullLogResponse t = -star
      ((1-2*criticalResponsePoint t)/(2*(criticalResponsePoint t*(1-criticalResponsePoint t))^(2 : ℕ))-
        deriv normalizedMinimumZeta (criticalResponsePoint t)-1/(12*(criticalResponsePoint t+1)^(2 : ℕ))) := by
  let c := criticalResponsePoint t
  let d := (1-2*c)/(2*(c*(1-c))^(2 : ℕ))-deriv normalizedMinimumZeta c-1/(12*(c+1)^(2 : ℕ))
  have hc : c ∈ minimumStrip := by norm_num [c,criticalResponsePoint,minimumStrip]
  have hf : HasDerivAt fullUnitHolomorphicSource d c := hasDerivAt_fullUnitHolomorphicSource hc
  have hp : HasDerivAt (fun h : ℝ => star (fullUnitHolomorphicSource (c+(h:ℂ)))) (star d) 0 := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (hf.comp_of_eq (0:ℂ) ((hasDerivAt_id (0:ℂ)).const_add c) (by simp)).comp_ofReal.star
  have hm : HasDerivAt (fun h : ℝ => star (fullUnitHolomorphicSource (c-(h:ℂ)))) (-star d) 0 := by
    simpa only [Function.comp_def,Pi.sub_apply,id_eq,zero_sub,mul_neg_one,star_neg] using
      (hf.comp_of_eq (0:ℂ) ((hasDerivAt_const (0:ℂ) c).sub (hasDerivAt_id (0:ℂ))) (by simp)).comp_ofReal.star
  have hg := ((hp.sub hm).tendsto_slope_zero).const_mul (1/2:ℂ)
  have hq : Tendsto (criticalResponseQuotient t) (𝓝[≠] (0:ℝ)) (𝓝 (star d)) := by
    have hval : (1/2:ℂ)*(star d- -star d)=star d := by ring
    rw [hval] at hg
    apply hg.congr'
    have hh : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), |h|<1/2 :=
      (continuous_abs.tendsto 0).eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with h hh
    have hab := abs_lt.mp hh
    have hpstrip : c+(h:ℂ) ∈ minimumStrip := by
      constructor <;> simp only [Complex.add_re,Complex.ofReal_re,c,criticalResponsePoint,
        Complex.div_ofNat_re,Complex.one_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] <;> linarith
    have hmstrip : c-(h:ℂ) ∈ minimumStrip := by
      constructor <;> simp only [Complex.sub_re,Complex.ofReal_re,c,criticalResponsePoint,
        Complex.add_re,Complex.div_ofNat_re,Complex.one_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] <;> linarith
    unfold criticalResponseQuotient
    rw [unitFullFourierSource_eq_star_holomorphic hpstrip,unitFullFourierSource_eq_star_holomorphic hmstrip]
    simp only [Pi.sub_apply,zero_add,Complex.ofReal_zero,add_zero,sub_zero,sub_self,
      Complex.real_smul]
    push_cast
    ring
  have he := tendsto_nhds_unique (tendsto_criticalResponseQuotient t) hq
  change -criticalFullLogResponse t=star d at he
  change criticalFullLogResponse t= -star d
  exact neg_eq_iff_eq_neg.mp he

/-- The critical boundary product has an explicit real value. -/
theorem criticalResponsePoint_product (t : ℝ) :
    criticalResponsePoint t*(1-criticalResponsePoint t)=((t^(2 : ℕ)+1/4:ℝ):ℂ) := by
  apply Complex.ext <;> simp [criticalResponsePoint,Complex.mul_re,Complex.mul_im,pow_two] <;> ring

/-- The reflected norm denominator on the critical line is explicit. -/
theorem criticalResponsePoint_normSq (t : ℝ) :
    Complex.normSq (star (criticalResponsePoint t)*(1-star (criticalResponsePoint t)))=(t^(2 : ℕ)+1/4)^(2 : ℕ) := by
  have he := congrArg star (criticalResponsePoint_product t)
  simp only [star_mul,star_sub,star_one,Complex.star_def,Complex.conj_ofReal] at he
  rw [mul_comm] at he
  rw [Complex.star_def,he,Complex.normSq_ofReal]
  ring

/-- At the critical point the exact zero target is the derivative of the rational source terms. -/
theorem reflectionZeroTarget_critical_eq (t : ℝ) :
    reflectionZeroTarget (criticalResponsePoint t)=star
      ((1-2*criticalResponsePoint t)/(2*(criticalResponsePoint t*(1-criticalResponsePoint t))^(2 : ℕ))-
        1/(12*(criticalResponsePoint t+1)^(2 : ℕ))) := by
  let c := criticalResponsePoint t
  have hcim : c.im=t := by simp [c,criticalResponsePoint]
  have hmirror : 2-c=star c+1 := by
    apply Complex.ext
    · simp [c,criticalResponsePoint]; ring
    · simp [c,criticalResponsePoint]
  have hB : star ((1-2*c)/(2*(c*(1-c))^(2 : ℕ)))=
      (((t/Complex.normSq (star c*(1-star c)):ℝ):ℂ)*Complex.I) := by
    have hp := criticalResponsePoint_product t
    have hn := criticalResponsePoint_normSq t
    change c*(1-c)=((t^(2 : ℕ)+1/4:ℝ):ℂ) at hp
    change Complex.normSq (star c*(1-star c))=(t^(2 : ℕ)+1/4)^(2 : ℕ) at hn
    have hnum : 1-2*c= -2*(t:ℂ)*Complex.I := by
      dsimp [c,criticalResponsePoint]; ring
    rw [hp,hn,hnum]
    simp only [star_div₀,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal,
      map_neg,map_ofNat,Complex.conj_I]
    have ha : (((t^(2 : ℕ)+1/4:ℝ):ℂ))≠0 := by
      exact_mod_cast (show t^(2 : ℕ)+(1/4:ℝ)≠0 by nlinarith [sq_nonneg t])
    push_cast at ha ⊢
    field_simp [ha]
  have hM : star (1/(12*(c+1)^(2 : ℕ)))=1/(12*(star c+1)*(2-c)) := by
    rw [hmirror]
    simp [pow_two]
    ring
  change reflectionZeroTarget c=star (_-_)
  rw [star_sub,hB,hM]
  exact congrArg (fun y : ℝ => (((y/Complex.normSq (star c*(1-star c)):ℝ):ℂ)*Complex.I-
    1/(12*(star c+1)*(2-c)))) hcim

/-- Exact arithmetic cancellation identifies the critical response with the normalized zeta derivative. -/
theorem criticalFullLogResponse_add_target_eq_derivative (t : ℝ) :
    criticalFullLogResponse t+reflectionZeroTarget (criticalResponsePoint t)=
      star (deriv normalizedMinimumZeta (criticalResponsePoint t)) := by
  rw [criticalFullLogResponse_eq_neg_star_source_derivative,reflectionZeroTarget_critical_eq]
  simp only [star_sub]
  ring

/-- At a critical zero, the response carries the unmodified zeta derivative and its normalization. -/
theorem criticalFullLogResponse_add_target_at_zero (t : ℝ)
    (hz : riemannZeta (criticalResponsePoint t)=0) :
    criticalFullLogResponse t+reflectionZeroTarget (criticalResponsePoint t)=
      star (deriv riemannZeta (criticalResponsePoint t)/
        (criticalResponsePoint t*(criticalResponsePoint t+1))) := by
  let c := criticalResponsePoint t
  have hc : c∈minimumStrip := by norm_num [c,criticalResponsePoint,minimumStrip]
  have hd := unitPhaseStrip_denominators hc
  have hq : HasDerivAt normalizedMinimumZeta (deriv riemannZeta c/(c*(c+1))) c := by
    convert! ((unitPhaseZeta_analytic c hc).differentiableAt.hasDerivAt).fun_div
      ((hasDerivAt_id c).mul ((hasDerivAt_id c).add_const (1:ℂ)))
      (mul_ne_zero hd.1 hd.2.2) using 1
    have hz' : riemannZeta c=0 := hz
    simp only [Pi.mul_apply,id_eq,hz',zero_mul,sub_zero]
    field_simp
  rw [criticalFullLogResponse_add_target_eq_derivative,hq.deriv]

/-- At a critical zero, response vanishing is exactly vanishing of the zeta derivative. -/
theorem critical_zero_response_eq_zero_iff (t : ℝ)
    (hz : riemannZeta (criticalResponsePoint t)=0) :
    criticalFullLogResponse t+reflectionZeroTarget (criticalResponsePoint t)=0 ↔
      deriv riemannZeta (criticalResponsePoint t)=0 := by
  have hc : criticalResponsePoint t∈minimumStrip := by norm_num [criticalResponsePoint,minimumStrip]
  have hd := unitPhaseStrip_denominators hc
  rw [criticalFullLogResponse_add_target_at_zero t hz,star_eq_zero,div_eq_zero_iff]
  exact or_iff_left (mul_ne_zero hd.1 hd.2.2)

/-- The exact even correction of the complete target when moving away from the critical line. -/
def reflectionTargetQuadraticCorrection (s : ℂ) : ℂ :=
  let c := criticalResponsePoint s.im
  let denominator := Complex.normSq (star s*(1-star s))*Complex.normSq (star c*(1-star c))
  ((s.im*(2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ))/denominator:ℝ):ℂ)*Complex.I+
    1/(12*(star c+1)^(2 : ℕ)*((star c+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)))

/-- The norm denominator changes by an exact quadratic-in-displacement polynomial. -/
theorem reflection_normSq_quadratic_difference (s : ℂ) :
    Complex.normSq (star s*(1-star s))-
      Complex.normSq (star (criticalResponsePoint s.im)*(1-star (criticalResponsePoint s.im)))=
        (s.re-1/2)^(2 : ℕ)*(2*s.im^(2 : ℕ)-1/2+(s.re-1/2)^(2 : ℕ)) := by
  rw [criticalResponsePoint_normSq]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

/-- The full reflected mean has the same exact even displacement variable. -/
theorem reflection_mean_quadratic_difference (s : ℂ) :
    (star (criticalResponsePoint s.im)+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)=(star s+1)*(2-s) := by
  apply Complex.ext <;> simp [criticalResponsePoint,Complex.mul_re,Complex.mul_im,pow_two] <;> ring

/-- The complete zero target transports by an exact quadratic displacement correction. -/
theorem reflectionZeroTarget_sub_critical {s : ℂ} (hs : s∈minimumStrip) :
    reflectionZeroTarget s-reflectionZeroTarget (criticalResponsePoint s.im)=
      -(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)*reflectionTargetQuadraticCorrection s := by
  let c := criticalResponsePoint s.im
  let C := Complex.normSq (star s*(1-star s))
  let C₀ := Complex.normSq (star c*(1-star c))
  let d : ℝ := (s.re-1/2)^(2 : ℕ)
  let q : ℂ := (star c+1)^(2 : ℕ)
  have hcim : c.im=s.im := by simp [c,criticalResponsePoint]
  have hmirror : 2-c=star c+1 := by
    apply Complex.ext
    · simp [c,criticalResponsePoint]; ring
    · simp [c,criticalResponsePoint]
  have hs0 : star s≠0 := by simpa using (unitPhaseStrip_denominators hs).1
  have hs1 : 1-star s≠0 := by
    intro h; have hr := congrArg Complex.re h; simp at hr; linarith [hs.2]
  have hC : C≠0 := (Complex.normSq_pos.mpr (mul_ne_zero hs0 hs1)).ne'
  have hC₀ : C₀≠0 := by
    change Complex.normSq (star (criticalResponsePoint s.im)*(1-star (criticalResponsePoint s.im)))≠0
    rw [criticalResponsePoint_normSq]
    positivity
  have ha : star s+1≠0 := by
    intro h; have hr := congrArg Complex.re h; simp at hr; linarith [hs.1]
  have hb : 2-s≠0 := by
    intro h; have hr := congrArg Complex.re h; simp at hr; linarith [hs.2]
  have hac : star c+1≠0 := by
    intro h; have hr := congrArg Complex.re h
    norm_num [c,criticalResponsePoint] at hr
  have hq : q≠0 := pow_ne_zero 2 hac
  have hqd : q-(d:ℂ)≠0 := by
    change (star (criticalResponsePoint s.im)+1)^(2 : ℕ)-(((s.re-1/2)^(2 : ℕ):ℝ):ℂ)≠0
    rw [reflection_mean_quadratic_difference]
    exact mul_ne_zero ha hb
  have hdC : C-C₀=d*(2*s.im^(2 : ℕ)-1/2+d) := reflection_normSq_quadratic_difference s
  have hheight : s.im/C-s.im/C₀= -d*(s.im*(2*s.im^(2 : ℕ)-1/2+d)/(C*C₀)) := by
    field_simp [hC,hC₀]
    have hh := congrArg (fun x : ℝ => s.im*x) hdC
    nlinarith only [hh]
  have hmeanS : 12*(star s+1)*(2-s)=12*(q-(d:ℂ)) := by
    have h := reflection_mean_quadratic_difference s
    change q-(d:ℂ)=(star s+1)*(2-s) at h
    rw [h]; ring
  have hmeanC : 12*(star c+1)*(2-c)=12*q := by rw [hmirror]; dsimp [q]; ring
  have hmean : (1:ℂ)/(12*(q-(d:ℂ)))-1/(12*q)=(d:ℂ)/(12*q*(q-(d:ℂ))) := by
    field_simp [hq,hqd]
    ring
  change reflectionZeroTarget s-reflectionZeroTarget c= -((d:ℝ):ℂ)*_
  unfold reflectionZeroTarget
  rw [hcim,hmeanS,hmeanC]
  change ((s.im/C:ℝ):ℂ)*Complex.I-1/(12*(q-(d:ℂ)))-
    (((s.im/C₀:ℝ):ℂ)*Complex.I-1/(12*q))= -((d:ℝ):ℂ)*_
  have hh := congrArg (fun x : ℝ => (x:ℂ)*Complex.I) hheight
  push_cast at hh
  unfold reflectionTargetQuadraticCorrection
  change ((s.im/C:ℝ):ℂ)*Complex.I-1/(12*(q-(d:ℂ)))-
    (((s.im/C₀:ℝ):ℂ)*Complex.I-1/(12*q))=
      -(d:ℂ)*(((s.im*(2*s.im^(2 : ℕ)-1/2+d)/(C*C₀):ℝ):ℂ)*Complex.I+1/(12*q*(q-(d:ℂ))))
  push_cast
  linear_combination hh-hmean

/-- The actual off-line response consists of the critical derivative and its exact even correction. -/
theorem reflectionDiskSource_eq_derivative_correction {s : ℂ} (hs : s∈minimumStrip) :
    reflectionDiskSource s=star (deriv normalizedMinimumZeta (criticalResponsePoint s.im))-
      (((s.re-1/2)^(2 : ℕ):ℝ):ℂ)*reflectionTargetQuadraticCorrection s := by
  have ht := reflectionZeroTarget_sub_critical hs
  have hd := criticalFullLogResponse_add_target_eq_derivative s.im
  change criticalFullLogResponse s.im+reflectionZeroTarget s=_
  linear_combination ht+hd

/-- Every actual off-line strip zero requires a quantitative critical normalized-derivative balance. -/
theorem normalized_derivative_constraint_at_offline_zero {s : ℂ} (hs : s∈minimumStrip)
    (hd : s.re≠1/2) (hz : riemannZeta s=0) :
    ‖star (deriv normalizedMinimumZeta (criticalResponsePoint s.im))-
      (((s.re-1/2)^(2 : ℕ):ℝ):ℂ)*reflectionTargetQuadraticCorrection s‖ ≤ (s.re-1/2)^(2 : ℕ)/12 := by
  rw [←reflectionDiskSource_eq_derivative_correction hs]
  exact norm_criticalFullLogResponse_zero_constraint hs.1 hs.2 hd hz

/-- The complete height-saving error also constrains the same literal normalized derivative. -/
theorem normalized_derivative_height_constraint_at_offline_zero {s : ℂ} (hs : s∈minimumStrip)
    (hd : s.re≠1/2) (ht : s.im≠0) (hz : riemannZeta s=0) :
    ‖star (deriv normalizedMinimumZeta (criticalResponsePoint s.im))-
      (((s.re-1/2)^(2 : ℕ):ℝ):ℂ)*reflectionTargetQuadraticCorrection s‖ ≤
        (s.re-1/2)^(2 : ℕ)*reflectionCubicHeightCost (1/2-|s.re-1/2|)/(2*|s.im|) := by
  rw [←reflectionDiskSource_eq_derivative_correction hs]
  exact norm_criticalFullLogResponse_zero_constraint_height hs.1 hs.2 hd ht hz

/-- The full compensated arithmetic current reconstructs the scaled critical derivative after exact target cancellation. -/
theorem tendsto_criticalLogSecondCurrent_derivative (t : ℝ) :
    Tendsto (fun m : ℕ => criticalLogSecondCurrent t m+
      ((t^(2 : ℕ):ℝ):ℂ)*reflectionZeroTarget (criticalResponsePoint t)-1/12) atTop
        (𝓝 (((t^(2 : ℕ):ℝ):ℂ)*star (deriv normalizedMinimumZeta (criticalResponsePoint t)))) := by
  have h := ((tendsto_criticalLogSecondCurrent t).add_const
    (((t^(2 : ℕ):ℝ):ℂ)*reflectionZeroTarget (criticalResponsePoint t))).sub_const (1/12:ℂ)
  have hval : (1/12+((t^(2 : ℕ):ℝ):ℂ)*criticalFullLogResponse t)+
      ((t^(2 : ℕ):ℝ):ℂ)*reflectionZeroTarget (criticalResponsePoint t)-1/12=
        ((t^(2 : ℕ):ℝ):ℂ)*star (deriv normalizedMinimumZeta (criticalResponsePoint t)) := by
    have he := criticalFullLogResponse_add_target_eq_derivative t
    linear_combination ((t^(2 : ℕ):ℝ):ℂ)*he
  rw [hval] at h
  exact h

end RHTower.DeletionMixedRefinement
