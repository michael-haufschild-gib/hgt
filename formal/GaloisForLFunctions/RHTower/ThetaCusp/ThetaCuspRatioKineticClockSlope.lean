import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMinor
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearSlope : Poly :=
  (6-X Coord.U)*clockFlow 21 clearMinor-
    36*(X Coord.U)^2*(12+4*X Coord.U)*X Coord.K*X Coord.J*clearMinor

theorem clearSlope_expanded : clearSlope=
    (6-X Coord.U)*clockLie clearMinor+
      (90-21*X Coord.U)*(X Coord.U)^2*(12+4*X Coord.U)*X Coord.K*X Coord.J*clearMinor := by
  unfold clearSlope clockFlow
  norm_num [map_ofNat]
  ring

theorem square_seed_flow (v k z : ℂ) :
    eval (basePoint v k z) (squareLie seed)=6*(12*k+4)*v*z := by
  have hs : squareLie seed=6*squareField .K := by
    change flow squareField (C (6:ℂ)*X Coord.K-C (1:ℂ))=6*squareField .K
    rw [flow_sub75,flow_mul,flow_C,flow_X,flow_C]
    norm_num [map_ofNat]
  rw [hs]
  norm_num [squareField,basePoint]
  ring

theorem clearSlope_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearSlope=h^24*eval (basePoint v h⁻¹ z) ThetaRatioSquare.slope := by
  simp only [clearSlope,map_sub,map_mul,map_pow,map_ofNat,eval_X,basePoint]
  rw [clearMinor_flow h v z hh,clearMinor_eval h v z hh]
  simp only [ThetaRatioSquare.slope,map_sub,map_mul,map_ofNat,square_seed_flow]
  norm_num [seed,basePoint]
  field_simp [hh]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
