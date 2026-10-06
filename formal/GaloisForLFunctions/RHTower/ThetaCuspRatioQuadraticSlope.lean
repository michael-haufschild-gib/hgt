import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticSource

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioQuadraticSource
open ThetaCuspModularRatio ThetaCuspOddDirectionTransport Filter Topology

theorem hasDerivAt_sixthNormalized {x : ℝ} (hx : 0 ≤ x) (P : Poly) :
    HasDerivAt (fun y => eval (state y) P/(eval (state y) (sourceJet 0))^6)
      (eval (state x) (sixthSlope P)/(eval (state x) (sourceJet 0))^7) x := by
  have h0 := sourceZero_ne hx
  have hd := (eval_derivative hx P).div
    ((eval_derivative hx (sourceJet 0)).pow 6) (pow_ne_zero 6 h0)
  simp only [Pi.pow_apply] at hd
  convert hd using 1 <;> first | rfl | skip
  simp only [sixthSlope,map_sub,map_mul,map_ofNat]
  field_simp [h0]
  ring

theorem normalizedB_slope {x : ℝ} (hx : 0 < x) :
    deriv normalizedB x=
      (eval (state x) (sixthSlope minorB)/(eval (state x) (sourceJet 0))^7).re := by
  have hd := hasDerivAt_sixthNormalized hx.le minorB
  have hn : HasDerivAt (fun y => (normalizedB y:ℂ))
      (eval (state x) (sixthSlope minorB)/(eval (state x) (sourceJet 0))^7) x := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact normalizedB_value hy.le
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hn
  change HasDerivAt normalizedB _ x at hr
  exact hr.deriv

theorem normalizedBase_slope (c : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (normalizedBase c) x=
      ((eval (state x) (slopeConstant (c:ℂ))+(x:ℂ)*eval (state x) (slopeLinear (c:ℂ)))/
        (eval (state x) (sourceJet 0))^7).re := by
  have h0 := sourceZero_ne hx.le
  have hd := (hasDerivAt_sixthNormalized hx.le (loadedConstant (c:ℂ))).add
    ((hasDerivAt_id' x).ofReal_comp.mul
      (hasDerivAt_sixthNormalized hx.le (loadedLinear (c:ℂ))))
  have hf : HasDerivAt (fun y =>
      eval (state y) (loadedConstant (c:ℂ))/(eval (state y) (sourceJet 0))^6+
      (y:ℂ)*(eval (state y) (loadedLinear (c:ℂ))/(eval (state y) (sourceJet 0))^6))
      ((eval (state x) (slopeConstant (c:ℂ))+(x:ℂ)*eval (state x) (slopeLinear (c:ℂ)))/
        (eval (state x) (sourceJet 0))^7) x := by
    convert hd using 1 <;> first | rfl | skip
    simp only [slopeConstant,slopeLinear,map_add,map_mul,Complex.ofReal_one]
    field_simp [h0]
    ring
  have hn : HasDerivAt (fun y => (normalizedBase c y:ℂ))
      ((eval (state x) (slopeConstant (c:ℂ))+(x:ℂ)*eval (state x) (slopeLinear (c:ℂ)))/
        (eval (state x) (sourceJet 0))^7) x := by
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [normalizedBase_value c hy.le]
    ring
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hn
  change HasDerivAt (normalizedBase c) _ x at hr
  exact hr.deriv

theorem normalized_source_quadratic (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (normalizedBase c) x+2*deriv normalizedB x*eta+deriv normalizedD x*eta^2=
      (eval (state x) (sourceQuadratic (c:ℂ) (x:ℂ) (eta:ℂ))/
        (eval (state x) (sourceJet 0))^7).re := by
  rw [normalizedBase_slope c hx,normalizedB_slope hx,normalized_third_slope hx]
  have hp : eval (state x) (sourceJet 0)=(k x:ℂ)-1/6 := by
    simp only [sourceJet_zero_eval,state]
  rw [←hp]
  have he :
      (eval (state x) (slopeConstant (c:ℂ))+(x:ℂ)*eval (state x) (slopeLinear (c:ℂ)))/
        (eval (state x) (sourceJet 0))^7+
      ((2*eta:ℝ):ℂ)*(eval (state x) (sixthSlope minorB)/(eval (state x) (sourceJet 0))^7)+
      ((eta^2:ℝ):ℂ)*(eval (state x) thirdSlope/(eval (state x) (sourceJet 0))^7)=
      eval (state x) (sourceQuadratic (c:ℂ) (x:ℂ) (eta:ℂ))/(eval (state x) (sourceJet 0))^7 := by
    simp only [sourceQuadratic,map_add,map_mul,eval_C,map_ofNat]
    push_cast
    ring
  have hr := congrArg Complex.re he
  simp only [Complex.add_re,Complex.re_ofReal_mul] at hr
  convert hr using 1
  ring

end
end RHTower.ThetaRatioSourceIncidence
