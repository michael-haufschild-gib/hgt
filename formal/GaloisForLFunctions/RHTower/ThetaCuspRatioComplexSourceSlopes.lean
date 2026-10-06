import GaloisForLFunctions.RHTower.ThetaCuspOddSeamRegularity

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
set_option autoImplicit false
open scoped ContDiff
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioQuadraticSource
open ThetaCuspModularRatio ThetaCuspOddDirectionTransport Filter Topology

theorem normalizedB_slope_complex {x : ℝ} (hx : 0 < x) :
    ((deriv normalizedB x:ℝ):ℂ)=
      (eval (state x) (sixthSlope minorB)/(eval (state x) (sourceJet 0))^7) := by
  have hd := hasDerivAt_sixthNormalized hx.le minorB
  have hn : HasDerivAt (fun y => (normalizedB y:ℂ))
      (eval (state x) (sixthSlope minorB)/(eval (state x) (sourceJet 0))^7) x := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact normalizedB_value hy.le
  exact (((ThetaCuspUpperSeam.normalizedB_regular.1.differentiable (by simp) x).hasDerivAt).ofReal_comp).unique hn

theorem normalizedBase_slope_complex (c : ℝ) {x : ℝ} (hx : 0 < x) :
    ((deriv (normalizedBase c) x:ℝ):ℂ)=
      ((eval (state x) (slopeConstant (c:ℂ))+(x:ℂ)*eval (state x) (slopeLinear (c:ℂ)))/
        (eval (state x) (sourceJet 0))^7) := by
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
  exact ((((ThetaCuspUpperSeam.normalizedBase_regular c).1.differentiable (by simp) x).hasDerivAt).ofReal_comp).unique hn

theorem centerDrive_slope_complex (c : ℝ) {x : ℝ} (hx : 0 < x) :
    ((deriv (ThetaCuspHeadGrowth.centerDrive c) x:ℝ):ℂ)=
      (eval (state x) (slopeLinear (c:ℂ))/(eval (state x) (sourceJet 0))^7) := by
  have hd := hasDerivAt_sixthNormalized hx.le (loadedLinear (c:ℂ))
  have hn : HasDerivAt (fun y => (ThetaCuspHeadGrowth.centerDrive c y:ℂ))
      (eval (state x) (slopeLinear (c:ℂ))/(eval (state x) (sourceJet 0))^7) x := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact centerDrive_value c hy.le
  exact ((((ThetaCuspUpperSeam.centerDrive_smooth c).differentiable (by simp) x).hasDerivAt).ofReal_comp).unique hn

theorem normalizedD_slope_complex {x : ℝ} (hx : 0 < x) :
    ((deriv normalizedD x:ℝ):ℂ)=
      eval (state x) thirdSlope/(eval (state x) (sourceJet 0))^7 := by
  have hd := hasDerivAt_sixthNormalized hx.le thirdMinor
  have hn : HasDerivAt (fun y => (normalizedD y:ℂ))
      (eval (state x) thirdSlope/(eval (state x) (sourceJet 0))^7) x := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simpa only [sourceJet_zero_eval,state] using normalized_third hy.le
  exact (((ThetaCuspUpperSeam.normalizedD_regular.1.differentiable (by simp) x).hasDerivAt).ofReal_comp).unique hn

theorem normalized_source_quadratic_complex (c eta : ℝ) {x : ℝ} (hx : 0 < x) :
    ((deriv (normalizedBase c) x+2*deriv normalizedB x*eta+
      deriv normalizedD x*eta^2:ℝ):ℂ)=
      eval (state x) (sourceQuadratic (c:ℂ) (x:ℂ) (eta:ℂ))/
        (eval (state x) (sourceJet 0))^7 := by
  push_cast
  rw [normalizedBase_slope_complex c hx,normalizedB_slope_complex hx,
    normalizedD_slope_complex hx]
  simp only [sourceQuadratic,map_add,map_mul,eval_C,map_ofNat]
  ring

end
end RHTower.ThetaRatioSourceIncidence
