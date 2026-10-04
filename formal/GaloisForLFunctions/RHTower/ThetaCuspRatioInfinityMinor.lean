import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityMoment2
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityMoment4
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityMoment6
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityMoment8
import GaloisForLFunctions.RHTower.ThetaCuspRatioInfinityMoment10
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def principalMass : ℂ := (6:ℂ)^24*1990656*1679616

def scaledMinor : Poly :=
  -scaledMoment2*scaledMoment6*scaledMoment10+
  scaledMoment2*scaledMoment8^2+scaledMoment4^2*scaledMoment10-
  2*X Coord.U*scaledMoment4*scaledMoment6*scaledMoment8+
  (X Coord.U)^2*scaledMoment6^3

theorem scaledMinor_eq (h r t : ℂ) (hh : h≠0) :
    h^17*eval (sourcePoint h r t) minor=eval (basePoint h r t) scaledMinor := by
  have he : h^17*eval (sourcePoint h r t) minor=
      -(h^3*eval (sourcePoint h r t) moment2)*
        (h^5*eval (sourcePoint h r t) moment6)*(h^9*eval (sourcePoint h r t) moment10)+
      (h^3*eval (sourcePoint h r t) moment2)*(h^7*eval (sourcePoint h r t) moment8)^2+
      (h^4*eval (sourcePoint h r t) moment4)^2*(h^9*eval (sourcePoint h r t) moment10)-
      2*h*(h^4*eval (sourcePoint h r t) moment4)*(h^5*eval (sourcePoint h r t) moment6)*
        (h^7*eval (sourcePoint h r t) moment8)+
      h^2*(h^5*eval (sourcePoint h r t) moment6)^3 := by
    simp only [minor,map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat]
    ring
  simp only [scaledMoment2_eq h r t hh,scaledMoment4_eq h r t hh,
    scaledMoment6_eq h r t hh,scaledMoment8_eq h r t hh,
    scaledMoment10_eq h r t hh] at he
  simpa [scaledMinor,basePoint] using he

/-- The quadratic contributions cancel: the principal minor depends linearly on the expanding mode. -/
theorem scaledMinor_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledMinor=-principalMass*(r-12*t) := by
  simp only [scaledMinor,map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,
    eval_X,basePoint,scaledMoment2_zero,scaledMoment4_zero,scaledMoment6_zero,
    scaledMoment8_zero,scaledMoment10_zero]
  unfold principalMass
  ring

end
end HTGeometry.ThetaRatioInfinity
