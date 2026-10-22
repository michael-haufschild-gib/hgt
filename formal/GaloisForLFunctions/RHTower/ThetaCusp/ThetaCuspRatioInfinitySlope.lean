import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinityMinor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinityCurve
/-! # Exact source-flow compactification and the third-slope expanding mode. -/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology


def clockLinear : Poly := C (-4/3:ℂ)*X Coord.U*(3+X Coord.U)*driftSquare*deficit

theorem clock_factor : infinityField Coord.U=X Coord.U*clockLinear := by
  unfold infinityField clockLinear
  ring

def scaledSlope : Poly :=
  (6-X Coord.U)*flow infinityField scaledMinor+
  (17*X Coord.U-66)*clockLinear*scaledMinor

theorem basePoint_eta (v : Coord → ℂ) : basePoint (v .U) (v .K) (v .J)=v := by
  funext i
  cases i <;> rfl

theorem scaledMinor_derivative (h r t : ℂ) (hh : h≠0) :
    eval (basePoint h r t) (flow infinityField scaledMinor)=
      17*h^16*vectorAt h r t Coord.U*eval (sourcePoint h r t) minor+
      h^18*eval (sourcePoint h r t) (squareLie minor) := by
  have dh := hasDerivAt_pi.mp (baseCurve_derivative h r t) Coord.U
  have hn := dh.continuousAt.eventually_ne (show baseCurve h r t 0 Coord.U≠0 by
    simpa [basePoint] using hh)
  have he : (fun z => eval (baseCurve h r t z) scaledMinor) =ᶠ[𝓝 0]
      (fun z => (baseCurve h r t z Coord.U)^17*eval (sourceCurve h r t z) minor) := by
    filter_upwards [hn] with z hz
    simpa only [sourceCurve,basePoint_eta] using
      (scaledMinor_eq (baseCurve h r t z .U) (baseCurve h r t z .K)
        (baseCurve h r t z .J) hz).symm
  have hd := ((dh.pow 17).mul (sourceEval_derivative minor h r t hh)).congr_of_eventuallyEq he
  have hu := (baseEval_derivative scaledMinor h r t).unique hd
  convert hu using 1 <;>
    simp only [Pi.pow_apply,baseCurve_zero,sourceCurve_zero,basePoint] <;> ring

theorem scaledSlope_eq (h r t : ℂ) (hh : h≠0) :
    h^19*eval (sourcePoint h r t) slope=eval (basePoint h r t) scaledSlope := by
  have hd := scaledMinor_derivative h r t hh
  have hp := scaledMinor_eq h r t hh
  have ht : vectorAt h r t Coord.U=h*eval (basePoint h r t) clockLinear := by
    simp [vectorAt,clock_factor,basePoint]
  have hc := (field_change h r t hh).2.1
  have hw : eval (sourcePoint h r t) (squareField Coord.K)=
      -eval (basePoint h r t) clockLinear/h^2 := by
    calc
      _ = (h*eval (sourcePoint h r t) (squareField Coord.K))/h := by field_simp [hh]
      _ = (-h⁻¹^2*vectorAt h r t Coord.U)/h := by rw [← hc]; rfl
      _ = _ := by rw [ht]; field_simp [hh]
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by
    ext i
    cases i <;> simp
  have hsL : squareLie seed=6*squareField Coord.K := by
    simp [squareLie,flow,seed,hu,pderiv_X,Pi.single_apply,pderiv_mul]
  have hs : eval (sourcePoint h r t) seed=(6-h)/h := by
    simp [seed,sourcePoint]
    field_simp [hh]
  simp only [ThetaRatioSquare.slope,scaledSlope,map_add,map_sub,map_mul,map_ofNat,eval_X,basePoint]
  rw [hs,hsL,map_mul,map_ofNat,hw,hd,← hp,ht]
  field_simp [hh]
  ring

theorem scaledMinor_derivative_zero (r t : ℂ) :
    eval (basePoint 0 r t) (flow infinityField scaledMinor)=
      -108*principalMass*(r-12*t) := by
  have hc (z : ℂ) : baseCurve 0 r t z=
      basePoint 0 (r+z*(-108*r)) (t+z*(-18*r+108*t)) := by
    funext i
    have hf := infinityField_zero r t
    cases i <;> simp [baseCurve,basePoint,vectorAt,hf.1,hf.2.1,hf.2.2]
  have he : (fun z => eval (baseCurve 0 r t z) scaledMinor)=
      (fun z => -principalMass*(r-12*t)+z*(-108*principalMass*(r-12*t))) := by
    funext z
    rw [hc,scaledMinor_zero]
    ring
  have hd := baseEval_derivative scaledMinor 0 r t
  rw [he] at hd
  have ha := ((hasDerivAt_id (0:ℂ)).mul_const (-108*principalMass*(r-12*t))).const_add
    (-principalMass*(r-12*t))
  simpa using hd.unique ha

theorem scaledSlope_zero (r t : ℂ) :
    eval (basePoint 0 r t) scaledSlope=-648*principalMass*(r-12*t) := by
  simp [scaledSlope,clockLinear,basePoint,scaledMinor_derivative_zero]
  ring

end
end HTGeometry.ThetaRatioInfinity
