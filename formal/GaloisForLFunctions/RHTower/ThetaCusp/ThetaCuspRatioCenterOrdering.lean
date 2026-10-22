import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddHeadGrowth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCenterEndpoints

namespace RHTower.ThetaRatioSourceIncidence
noncomputable section
set_option autoImplicit false
open MvPolynomial HTGeometry.ThetaRatioSource HTGeometry.ThetaRatioSquare
open HTGeometry.ThetaRatioQuadraticSource HTGeometry.ThetaRatioWeightedSquare
open HTGeometry.ThetaRatioInfinity ThetaCuspModularRatio Filter Topology

theorem centerDrive_value (c : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (ThetaCuspHeadGrowth.centerDrive c x:ℂ)=
      eval (state x) (loadedLinear (c:ℂ))/(eval (state x) (sourceJet 0))^6 := by
  have hp : (thetaCuspFullSource x:ℂ)=
      (sourceAmplitude x:ℂ)*eval (state x) (sourceJet 0) := by
    simpa only [iteratedDeriv_zero] using source_jet hx 0
  have hp1 : ((deriv thetaCuspFullSource x:ℝ):ℂ)=
      (sourceAmplitude x:ℂ)*eval (state x) (sourceJet 1) := by
    simpa only [iteratedDeriv_one] using source_jet hx 1
  unfold ThetaCuspHeadGrowth.centerDrive ThetaCuspHeadGrowth.normalizedHead
  rw [(hasDerivAt_thetaCuspLogSource x).deriv]
  simp only [iteratedDeriv_one]
  push_cast
  rw [native_headMinor hx,hp,hp1]
  simp only [loadedLinear,map_mul,map_ofNat,eval_C]
  field_simp [sourceAmplitude_ne hx,sourceZero_ne hx]

theorem centerDrive_slope (c : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (ThetaCuspHeadGrowth.centerDrive c) x=
      (eval (state x) (slopeLinear (c:ℂ))/(eval (state x) (sourceJet 0))^7).re := by
  have hd := hasDerivAt_sixthNormalized hx.le (loadedLinear (c:ℂ))
  have hn : HasDerivAt (fun y => (ThetaCuspHeadGrowth.centerDrive c y:ℂ))
      (eval (state x) (slopeLinear (c:ℂ))/(eval (state x) (sourceJet 0))^7) x := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact centerDrive_value c hy.le
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hn
  change HasDerivAt (ThetaCuspHeadGrowth.centerDrive c) _ x at hr
  exact hr.deriv

theorem actual_center_slope_eq (c : ℝ) {x : ℝ} (hx : 0 < x) :
    eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))=
      (6:ℂ)^30*(u x:ℂ)^26*eval (state x) (slopeLinear (c:ℂ)) := by
  let v : Coord → ℂ := fun i => match i with
    | .U => u x
    | .K => k x
    | .J => (J x:ℂ)/(u x:ℂ)
  have hu : (u x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)))
  have hsh : (eval v ∘ shearCoord)=state x := by
    funext i
    cases i <;> simp [shearCoord,state,v]
    field_simp [hu]
  have hsq : (eval v ∘ squareCoord)=actualSquarePoint x := by
    funext i
    cases i <;> simp [squareCoord,actualSquarePoint,v]
  have h1 (P : Poly) : eval v (shear P)=eval (state x) P := by
    simpa only [shear,coe_eval₂Hom,hsh] using (eval_assoc shearCoord v P).symm
  have h2 (P : Poly) : eval v (square P)=eval (actualSquarePoint x) P := by
    simpa only [square,coe_eval₂Hom,hsq] using (eval_assoc squareCoord v P).symm
  have he := congrArg (eval v)
    (weightedSixthSlope_eq 23 _ _ _ (weightedLoadedLinear_eq (c:ℂ)))
  rw [h2] at he
  simp only [map_mul,map_pow,eval_C,eval_X,h1,v] at he
  change eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))=
    (36*(6:ℂ)^28)*(u x:ℂ)^(23+3)*eval (state x) (slopeLinear (c:ℂ)) at he
  rw [he]
  ring

theorem actual_center_slope_neg {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (eval (actualSquarePoint x) (centerSlopeCoefficient (c:ℂ))).re < 0 := by
  have hn := ThetaCuspHeadGrowth.centerDrive_deriv_neg hc hx
  rw [centerDrive_slope c hx] at hn
  have hk : 0 < k x-1/6 := by linarith [k_gt hx.le]
  have hp : eval (state x) (sourceJet 0)=((k x-1/6:ℝ):ℂ) := by
    rw [sourceJet_zero_eval]
    change (k x:ℂ)-1/6=((k x-1/6:ℝ):ℂ)
    push_cast
    rfl
  rw [hp,←Complex.ofReal_pow,Complex.div_ofReal_re] at hn
  have hneg := mul_neg_of_neg_of_pos hn (pow_pos hk 7)
  rw [div_mul_cancel₀ _ (pow_ne_zero 7 hk.ne')] at hneg
  rw [actual_center_slope_eq c hx]
  have h6 : (6:ℂ)^30=(((6:ℝ)^30:ℝ):ℂ) := by norm_cast
  have hu26 : (u x:ℂ)^26=(((u x)^26:ℝ):ℂ) := by norm_cast
  rw [h6,hu26,←Complex.ofReal_mul,Complex.re_ofReal_mul]
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  exact mul_neg_of_pos_of_neg (by positivity) hneg

theorem actual_upper_center_quadratic_lt_lower {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (eta : ℝ) :
    (eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ))).re <
      (eval (actualSquarePoint x) (lowerCenterQuadratic (c:ℂ) (eta:ℂ))).re := by
  have hh : 0 < actualCenterUpper x :=
    (actual_center_ratio_bounds hx).1.trans_le (actual_center_ratio_bounds hx).2
  have hn := mul_neg_of_pos_of_neg hh (actual_center_slope_neg hc hx)
  simp only [upperCenterQuadratic,map_add,map_mul,actual_upper_center_eval,
    Complex.add_re,Complex.re_ofReal_mul]
  linarith only [hn]

theorem actual_upper_center_quadratic_le_source {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x) (eta : ℝ) :
    (eval (actualSquarePoint x) (upperCenterQuadratic (c:ℂ) (eta:ℂ))).re ≤
      (eval (actualSquarePoint x)
        (weightedSourceQuadratic (c:ℂ) ((x/u x:ℝ):ℂ) (eta:ℂ))).re := by
  have hcenter := (actual_center_ratio_bounds hx).2
  have hn := actual_center_slope_neg hc hx
  have hmul := mul_le_mul_of_nonpos_right hcenter hn.le
  rw [weightedSourceQuadratic_affine]
  simp only [upperCenterQuadratic,map_add,map_mul,eval_C,actual_upper_center_eval,
    Complex.add_re,Complex.re_ofReal_mul]
  linarith only [hmul]

end
end RHTower.ThetaRatioSourceIncidence
