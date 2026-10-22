import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMinorCore
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockSlope
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def compactSlope : Poly :=
  (6-X Coord.U)*defectLie compactMinor+
    18*X Coord.U*(4-X Coord.U)*(12+4*X Coord.U)*
      (9-X Coord.K*(X Coord.U)^2)*X Coord.J*compactMinor

theorem compactSlope_factor : defectLift clearSlope=(X Coord.U)^4*compactSlope := by
  rw [clearSlope_expanded]
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,defectLift_X,defectCoord]
  rw [←defectLie_lift,compactMinor_factor]
  simp only [defectLie,flow_mul,flow_pow75,flow_X]
  apply MvPolynomial.funext
  intro v
  norm_num [compactSlope,defectField,defectLie]
  ring

theorem compactSlope_eval (h r z : ℂ) (hh : h≠0) :
    eval (basePoint h r z) compactSlope=
      h^20*eval (basePoint (9-r*h^2) h⁻¹ z) slope := by
  have he := congrArg (eval (basePoint h r z)) compactSlope_factor
  rw [defectLift_eval,clearSlope_eval _ _ _ hh] at he
  simp only [map_mul,map_pow,eval_X,basePoint] at he
  apply mul_left_cancel₀ (pow_ne_zero 4 hh)
  calc
    _ = h^24*eval (basePoint (9-r*h^2) h⁻¹ z) slope := he.symm
    _ = _ := by ring

end
end HTGeometry.ThetaRatioKineticContraction
