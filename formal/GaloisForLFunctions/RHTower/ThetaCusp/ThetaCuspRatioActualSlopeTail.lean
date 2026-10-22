import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioAxisSlope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioFlatEvaluation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioThirdSlope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioIntegerIncidence
import Mathlib.Topology.Algebra.Polynomial

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology
open RHTower RHTower.ThetaCuspModularRatio RHTower.ThetaRatioSourceIncidence


theorem actual_scaledSlope_tendsto :
    Tendsto (fun x => (k x:ℂ)^3*eval (actualBase x) scaledSlope)
      atTop (𝓝 (1944*axisMinorMass)) := by
  have hh : Tendsto (fun x => ((k x:ℂ))⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp inverse_k_tendsto_zero
  have ha : Tendsto (fun x => axisSlopeCore.eval ((k x:ℂ)⁻¹))
      atTop (𝓝 (1944*axisMinorMass)) := by
    simpa [axisSlopeCore_zero,Function.comp_def] using axisSlopeCore.continuous.tendsto (0:ℂ) |>.comp hh
  have he : (fun x => axisSlopeCore.eval ((k x:ℂ)⁻¹)) =ᶠ[atTop]
      (fun x => (k x:ℂ)^3*eval (axisBase x) scaledSlope) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have hk : (k x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [k_gt hx])
    simp only [axisBase,Complex.ofReal_inv,← axis_eval,axisSlope_factor,
      Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
    field_simp [hk]
  have hs := (actual_axis_polynomial_flat scaledSlope 3).add (ha.congr' he)
  convert hs using 1
  · funext x
    ring
  · simp

theorem actual_scaledSlope_eventually_pos :
    ∀ᶠ x in atTop, 0<((k x:ℂ)^3*eval (actualBase x) scaledSlope).re := by
  have hl := (Complex.continuous_re.tendsto (1944*axisMinorMass)).comp
    actual_scaledSlope_tendsto
  apply hl.eventually_const_lt
  norm_num [axisMinorMass]

def actualSquarePoint (x : ℝ) : Coord → ℂ
  | .U => (u x:ℂ)^2
  | .K => k x
  | .J => (J x:ℂ)/(u x:ℂ)

theorem actual_sourcePoint {x : ℝ} (hx : 0≤x) :
    sourcePoint ((k x:ℂ)⁻¹) (kineticGap x:ℂ)
      ((k x*(1-3*J x/u x):ℝ):ℂ)=actualSquarePoint x := by
  have hk : (k x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [k_gt hx])
  funext i
  cases i <;> simp [sourcePoint,actualSquarePoint,kineticGap,t]
  all_goals field_simp [hk] <;> ring

theorem actualSquareSlope_eventually_pos :
    ∀ᶠ x in atTop, 0<(eval (actualSquarePoint x) ThetaRatioSquare.slope).re := by
  filter_upwards [actual_scaledSlope_eventually_pos,eventually_ge_atTop (0:ℝ)] with x hs hx
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx)
  have he := congrArg Complex.re (scaledSlope_eq ((k x:ℂ)⁻¹)
    (kineticGap x:ℂ) ((k x*(1-3*J x/u x):ℝ):ℂ)
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne')))
  rw [actual_sourcePoint hx] at he
  have hb : basePoint ((k x:ℂ)⁻¹) (kineticGap x:ℂ)
      ((k x*(1-3*J x/u x):ℝ):ℂ)=actualBase x := by simp [actualBase]
  rw [hb] at he
  simp only [← Complex.ofReal_inv,← Complex.ofReal_pow,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs he
  have hp : 0<(eval (actualBase x) scaledSlope).re := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hk.le 3) (le_of_not_gt hn)
    linarith
  rw [← he] at hp
  by_contra hn
  have := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (inv_nonneg.mpr hk.le) 19)
    (le_of_not_gt hn)
  linarith

theorem actualSquareSlope_incidence {x : ℝ} (hx : 0<x) :
    eval (actualSquarePoint x) ThetaRatioSquare.slope=
      (u x:ℂ)*(6:ℂ)^26*eval (state x) thirdSlope := by
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
  have hs := congrArg (eval v) ThetaRatioSquare.slope_eq
  have h1 (P : Poly) : eval v (shear P)=eval (state x) P := by
    simpa only [shear,coe_eval₂Hom,hsh] using (eval_assoc shearCoord v P).symm
  have h2 (P : Poly) : eval v (square P)=eval (actualSquarePoint x) P := by
    simpa only [square,coe_eval₂Hom,hsq] using (eval_assoc squareCoord v P).symm
  rw [map_mul,eval_X,h1,h2,integerThirdSlope_eq,map_mul,eval_C] at hs
  simpa only [v,mul_assoc] using hs.symm

theorem normalized_third_slope_eventually_pos :
    ∀ᶠ x in atTop, 0<deriv ThetaCuspOddDirectionTransport.normalizedD x := by
  filter_upwards [actualSquareSlope_eventually_pos,eventually_gt_atTop (0:ℝ)] with x hs hx
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0<k x-1/6 := by linarith [k_gt hx.le]
  rw [actualSquareSlope_incidence hx] at hs
  have h6 : (6:ℂ)^26=(((6:ℝ)^26:ℝ):ℂ) := by norm_cast
  rw [h6] at hs
  simp only [← Complex.ofReal_mul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  have hn : 0<(eval (state x) thirdSlope).re := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (show 0≤u x*(6:ℝ)^26 by positivity)
      (le_of_not_gt hn)
    linarith
  rw [normalized_third_slope hx]
  have hd : ((k x:ℂ)-1/6)^7=(((k x-1/6)^7:ℝ):ℂ) := by push_cast; rfl
  rw [hd,Complex.div_ofReal_re]
  exact div_pos hn (pow_pos hk 7)


end
end HTGeometry.ThetaRatioInfinity
