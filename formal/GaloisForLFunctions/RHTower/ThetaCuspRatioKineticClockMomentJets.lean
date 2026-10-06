import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticClockMoments
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem clearMoment2_zero (z : ℂ) :
    eval (basePoint 0 9 z) clearMoment2=-31104 := by
  norm_num [clearMoment2,clearMoment2Part0,clearMoment2Part1,basePoint]

theorem clearMoment4_zero (z : ℂ) :
    eval (basePoint 0 9 z) clearMoment4=0 := by
  norm_num [clearMoment4,clearMoment4Part0,clearMoment4Part1,clearMoment4Part2,clearMoment4Part3,basePoint]

theorem clearMoment4_first (z : ℂ) :
    eval (basePoint 0 9 z) (pderiv Coord.U clearMoment4)=12^5*3^5*(z+1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  norm_num [clearMoment4,clearMoment4Part0,clearMoment4Part1,clearMoment4Part2,clearMoment4Part3,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ]
  ring

theorem clearMoment6_zero (z : ℂ) :
    eval (basePoint 0 9 z) clearMoment6=0 := by
  norm_num [clearMoment6,clearMoment6Part0,clearMoment6Part1,clearMoment6Part2,clearMoment6Part3,clearMoment6Part4,clearMoment6Part5,clearMoment6Part6,clearMoment6Part7,basePoint]

theorem clearMoment6_first (z : ℂ) :
    eval (basePoint 0 9 z) (pderiv Coord.U clearMoment6)=12^7*3^6*(3*z-1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  norm_num [clearMoment6,clearMoment6Part0,clearMoment6Part1,clearMoment6Part2,clearMoment6Part3,clearMoment6Part4,clearMoment6Part5,clearMoment6Part6,clearMoment6Part7,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ]
  ring

theorem clearMoment8_zero (z : ℂ) :
    eval (basePoint 0 9 z) clearMoment8=0 := by
  norm_num [clearMoment8,clearMoment8Part0,clearMoment8Part1,clearMoment8Part2,clearMoment8Part3,clearMoment8Part4,clearMoment8Part5,clearMoment8Part6,clearMoment8Part7,clearMoment8Part8,clearMoment8Part9,clearMoment8Part10,clearMoment8Part11,clearMoment8Part12,clearMoment8Part13,basePoint]

theorem clearMoment8_first (z : ℂ) :
    eval (basePoint 0 9 z) (pderiv Coord.U clearMoment8)=12^9*3^8*(3*z-1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  norm_num [clearMoment8,clearMoment8Part0,clearMoment8Part1,clearMoment8Part2,clearMoment8Part3,clearMoment8Part4,clearMoment8Part5,clearMoment8Part6,clearMoment8Part7,clearMoment8Part8,clearMoment8Part9,clearMoment8Part10,clearMoment8Part11,clearMoment8Part12,clearMoment8Part13,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ]
  ring

theorem clearMoment10_zero (z : ℂ) :
    eval (basePoint 0 9 z) clearMoment10=0 := by
  norm_num [clearMoment10,clearMoment10Part0,clearMoment10Part1,clearMoment10Part2,clearMoment10Part3,clearMoment10Part4,clearMoment10Part5,clearMoment10Part6,clearMoment10Part7,clearMoment10Part8,clearMoment10Part9,clearMoment10Part10,clearMoment10Part11,clearMoment10Part12,clearMoment10Part13,clearMoment10Part14,clearMoment10Part15,clearMoment10Part16,clearMoment10Part17,clearMoment10Part18,clearMoment10Part19,clearMoment10Part20,clearMoment10Part21,clearMoment10Part22,basePoint]

theorem clearMoment10_first (z : ℂ) :
    eval (basePoint 0 9 z) (pderiv Coord.U clearMoment10)=12^11*3^10*(3*z-1) := by
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  norm_num [clearMoment10,clearMoment10Part0,clearMoment10Part1,clearMoment10Part2,clearMoment10Part3,clearMoment10Part4,clearMoment10Part5,clearMoment10Part6,clearMoment10Part7,clearMoment10Part8,clearMoment10Part9,clearMoment10Part10,clearMoment10Part11,clearMoment10Part12,clearMoment10Part13,clearMoment10Part14,clearMoment10Part15,clearMoment10Part16,clearMoment10Part17,clearMoment10Part18,clearMoment10Part19,clearMoment10Part20,clearMoment10Part21,clearMoment10Part22,basePoint,pderiv_X,Pi.single_apply,hUK,hUJ]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
