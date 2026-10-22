import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControlDifference
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticContraction
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem complete_clock_contraction_factor (h s e : ℂ) :
    eval (basePoint h (nonlinearBoundaryV h s) (e*nonlinearBoundaryZ h s)) clearSlope=
      h^4*nonlinearBoundaryV h s*eval (basePoint h s e) contractionSource := by
  have he := congrArg (eval (basePoint h (nonlinearBoundaryR h s) (e*nonlinearBoundaryZ h s)))
    compactSlope_factor
  rw [defectLift_eval,compactSlope_drift_factor] at he
  simp only [map_mul,map_pow,eval_X,basePoint] at he
  have hs : eval (basePoint h s e) contractionSource=
      eval (basePoint h (nonlinearBoundaryR h s) (e*nonlinearBoundaryZ h s)) compactReducedSlope := by
    rw [contractionSource,nonlinearBoundaryLift_eval]
    simp only [map_mul,eval_X,basePoint,boundaryZPoly_eval]
  rw [hs]
  simpa only [driftSquare,map_sub,map_mul,map_pow,map_ofNat,eval_X,basePoint,
    nonlinearBoundaryV,mul_assoc] using he

theorem contractionSource_difference (h s e : ℂ) :
    eval (basePoint h s e) contractionSource-eval (basePoint h s 1) contractionSource=
      (1-e)*eval (basePoint h s e) contractionRemainder := by
  have he := congrArg (eval (basePoint h s e)) (kineticOne_division contractionSource).choose_spec
  change eval (basePoint h s e) contractionSource=
    eval (basePoint h s e) ((1-X Coord.J)*contractionRemainder+kineticOne contractionSource) at he
  rw [map_add,map_mul,kineticOne_eval] at he
  simp only [map_sub,map_one,eval_X,basePoint] at he
  exact sub_eq_iff_eq_add.mpr he

def kineticBoundaryV (h s : ℝ) : ℝ := 9-s*(1-h^2*(1/12-7*h/72)*s)*h^2
def kineticBoundaryZ (h s : ℝ) : ℝ := (1-h*(1/12-7*h/72)*s)/3

theorem kineticBoundaryV_cast (h s : ℝ) :
    (kineticBoundaryV h s:ℂ)=nonlinearBoundaryV (h:ℂ) (s:ℂ) := by
  unfold kineticBoundaryV nonlinearBoundaryV nonlinearBoundaryR nonlinearBoundarySeed
  push_cast
  ring

theorem kineticBoundaryZ_cast (h s : ℝ) :
    (kineticBoundaryZ h s:ℂ)=nonlinearBoundaryZ (h:ℂ) (s:ℂ) := by
  unfold kineticBoundaryZ nonlinearBoundaryZ nonlinearBoundaryT nonlinearBoundarySeed
  push_cast
  ring

theorem completeKineticValue_contraction (h s e : ℝ) :
    completeKineticValue h (kineticBoundaryV h s) (e*kineticBoundaryZ h s)=
      h^4*kineticBoundaryV h s*(eval (basePoint (h:ℂ) (s:ℂ) (e:ℂ)) contractionSource).re := by
  have he := congrArg Complex.re (complete_clock_contraction_factor (h:ℂ) (s:ℂ) (e:ℂ))
  rw [←kineticBoundaryV_cast,←kineticBoundaryZ_cast] at he
  simpa only [completeKineticValue,Complex.ofReal_mul,←Complex.ofReal_pow,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero,sub_zero] using he

theorem complete_control_source_remainder (h s e : ℝ) :
    (1-e)*kineticBernsteinDifference 19
        (completeKineticControl h (kineticBoundaryV h s) (kineticBoundaryZ h s)) e=
      h^4*kineticBoundaryV h s*(1-e)*
        (eval (basePoint (h:ℂ) (s:ℂ) (e:ℂ)) contractionRemainder).re := by
  rw [←complete_source_control_difference,completeKineticValue_contraction]
  have hb := completeKineticValue_contraction h s 1
  simp only [one_mul,Complex.ofReal_one] at hb
  rw [hb,←mul_sub]
  have he := congrArg Complex.re (contractionSource_difference (h:ℂ) (s:ℂ) (e:ℂ))
  simp only [Complex.sub_re,Complex.mul_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero,zero_mul] at he
  rw [he]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
