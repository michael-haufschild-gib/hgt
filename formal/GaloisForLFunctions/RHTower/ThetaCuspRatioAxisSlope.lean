import GaloisForLFunctions.RHTower.ThetaCuspRatioAxisMoments
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinitySlope
import Mathlib.Algebra.Polynomial.Derivative

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare


def axisMoment8Core : Polynomial ℂ := (axis scaledMoment8).divX
def axisMoment10Core : Polynomial ℂ := (axis scaledMoment10).divX.divX

theorem axisMoment8_factor :
    axis scaledMoment8=Polynomial.X*axisMoment8Core := by
  simpa [axisMoment8Core,axisMoment8_coeff_zero] using
    (Polynomial.X_mul_divX_add (axis scaledMoment8)).symm

theorem axisMoment10_factor :
    axis scaledMoment10=Polynomial.X^2*axisMoment10Core := by
  have h1 : axis scaledMoment10=Polynomial.X*(axis scaledMoment10).divX := by
    simpa [axisMoment10_coeff_zero] using
      (Polynomial.X_mul_divX_add (axis scaledMoment10)).symm
  have h2 : (axis scaledMoment10).divX=Polynomial.X*axisMoment10Core := by
    simpa [axisMoment10Core,Polynomial.coeff_divX,axisMoment10_coeff_one] using
      (Polynomial.X_mul_divX_add (axis scaledMoment10).divX).symm
  rw [h1,h2]
  ring

theorem axisMoment8Core_zero : axisMoment8Core.eval 0=(6:ℂ)^10*105*24^4 := by
  simpa [axisMoment8Core,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_divX] using
    axisMoment8_coeff_one

theorem axisMoment10Core_zero : axisMoment10Core.eval 0= -(6:ℂ)^12*945*24^5 := by
  simpa [axisMoment10Core,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_divX] using
    axisMoment10_coeff_two

def axisMinorMass : ℂ := (6:ℂ)^24*24^9*720

def axisMinorCore : Polynomial ℂ :=
  -axis scaledMoment2*axis scaledMoment6*axisMoment10Core+
  axis scaledMoment2*axisMoment8Core^2+
  (axis scaledMoment4)^2*axisMoment10Core-
  2*axis scaledMoment4*axis scaledMoment6*axisMoment8Core+
  (axis scaledMoment6)^3

theorem axisMinor_factor : axis scaledMinor=Polynomial.X^2*axisMinorCore := by
  simp only [scaledMinor,map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,axis_X,axisCoord]
  rw [axisMoment8_factor,axisMoment10_factor]
  unfold axisMinorCore
  ring

theorem axisMinorCore_zero : axisMinorCore.eval 0=axisMinorMass := by
  simp [axisMinorCore,axis_eval,scaledMoment2_zero,scaledMoment4_zero,scaledMoment6_zero,
    axisMoment8Core_zero,axisMoment10Core_zero,axisMinorMass]
  ring

theorem axis_field (i : Coord) : axis (infinityField i)=
    match i with
    | .U => -(36:Polynomial ℂ)*Polynomial.X^2-12*Polynomial.X^3
    | .K => 0
    | .J => 0 := by
  cases i <;> apply Polynomial.funext <;> intro h
  all_goals norm_num [infinityField,axis,axisCoord,driftSquare,deficit,speed] <;> ring

theorem axis_flow (P : Poly) :
    axis (flow infinityField P)=
      (-(36:Polynomial ℂ)*Polynomial.X^2-12*Polynomial.X^3)*(axis P).derivative := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [flow_C]
  | add p q hp hq =>
    simp only [flow_add,map_add,hp,hq]
    ring
  | mul_X p i hp =>
    simp only [flow_mul,flow_X,map_add,map_mul,Polynomial.derivative_mul,hp,axis_field,axis_X]
    cases i <;> simp [axisCoord] <;> ring

def axisSlopeCore : Polynomial ℂ :=
  (-36-12*Polynomial.X)*
    ((6-Polynomial.X)*(2*axisMinorCore+Polynomial.X*axisMinorCore.derivative)+
      (17*Polynomial.X-66)*axisMinorCore)

theorem axisSlope_factor : axis scaledSlope=Polynomial.X^3*axisSlopeCore := by
  have hc : axis clockLinear=Polynomial.X*(-36-12*Polynomial.X) := by
    apply Polynomial.funext
    intro h
    norm_num [clockLinear,axis,axisCoord,driftSquare,deficit]
    ring
  simp only [scaledSlope,map_add,map_sub,map_mul,map_ofNat,axis_X,axisCoord]
  rw [axis_flow,axisMinor_factor,hc]
  simp only [Polynomial.derivative_mul,Polynomial.derivative_pow,Polynomial.derivative_X]
  unfold axisSlopeCore
  norm_num [Polynomial.C_ofNat]
  ring

theorem axisSlopeCore_zero : axisSlopeCore.eval 0=1944*axisMinorMass := by
  simp [axisSlopeCore,axisMinorCore_zero]
  ring


end
end HTGeometry.ThetaRatioInfinity
