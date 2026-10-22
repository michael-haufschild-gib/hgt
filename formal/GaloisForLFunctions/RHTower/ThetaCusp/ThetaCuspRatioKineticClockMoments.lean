import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockAlgebra
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticClockMoment10
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def clearMoment2 : Poly := (clearMoment2Part0 + clearMoment2Part1)

theorem clearMoment2_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment2=h^3*eval (basePoint v h⁻¹ z) moment2 := by
  simp only [clearMoment2,moment2,map_add,clearMoment2Part0_eval h v z hh,clearMoment2Part1_eval h v z hh]
  ring

theorem clearMoment2_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 3 clearMoment2)=
      h^5*eval (basePoint v h⁻¹ z) (squareLie moment2) := by
  simp only [clearMoment2,clockFlow_add,map_add,clearMoment2Part0_flow h v z hh,clearMoment2Part1_flow h v z hh]
  simp only [moment2,squareLie,flow_add,map_add]
  ring

def clearMoment4 : Poly := ((clearMoment4Part0 + clearMoment4Part1) + (clearMoment4Part2 + clearMoment4Part3))

theorem clearMoment4_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment4=h^5*eval (basePoint v h⁻¹ z) moment4 := by
  simp only [clearMoment4,moment4,map_add,clearMoment4Part0_eval h v z hh,clearMoment4Part1_eval h v z hh,clearMoment4Part2_eval h v z hh,clearMoment4Part3_eval h v z hh]
  ring

theorem clearMoment4_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 5 clearMoment4)=
      h^7*eval (basePoint v h⁻¹ z) (squareLie moment4) := by
  simp only [clearMoment4,clockFlow_add,map_add,clearMoment4Part0_flow h v z hh,clearMoment4Part1_flow h v z hh,clearMoment4Part2_flow h v z hh,clearMoment4Part3_flow h v z hh]
  simp only [moment4,squareLie,flow_add,map_add]
  ring

def clearMoment6 : Poly := (((clearMoment6Part0 + clearMoment6Part1) + (clearMoment6Part2 + clearMoment6Part3)) + ((clearMoment6Part4 + clearMoment6Part5) + (clearMoment6Part6 + clearMoment6Part7)))

theorem clearMoment6_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment6=h^7*eval (basePoint v h⁻¹ z) moment6 := by
  simp only [clearMoment6,moment6,map_add,clearMoment6Part0_eval h v z hh,clearMoment6Part1_eval h v z hh,clearMoment6Part2_eval h v z hh,clearMoment6Part3_eval h v z hh,clearMoment6Part4_eval h v z hh,clearMoment6Part5_eval h v z hh,clearMoment6Part6_eval h v z hh,clearMoment6Part7_eval h v z hh]
  ring

theorem clearMoment6_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 7 clearMoment6)=
      h^9*eval (basePoint v h⁻¹ z) (squareLie moment6) := by
  simp only [clearMoment6,clockFlow_add,map_add,clearMoment6Part0_flow h v z hh,clearMoment6Part1_flow h v z hh,clearMoment6Part2_flow h v z hh,clearMoment6Part3_flow h v z hh,clearMoment6Part4_flow h v z hh,clearMoment6Part5_flow h v z hh,clearMoment6Part6_flow h v z hh,clearMoment6Part7_flow h v z hh]
  simp only [moment6,squareLie,flow_add,map_add]
  ring

def clearMoment8 : Poly := (((clearMoment8Part0 + (clearMoment8Part1 + clearMoment8Part2)) + ((clearMoment8Part3 + clearMoment8Part4) + (clearMoment8Part5 + clearMoment8Part6))) + ((clearMoment8Part7 + (clearMoment8Part8 + clearMoment8Part9)) + ((clearMoment8Part10 + clearMoment8Part11) + (clearMoment8Part12 + clearMoment8Part13))))

theorem clearMoment8_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment8=h^9*eval (basePoint v h⁻¹ z) moment8 := by
  simp only [clearMoment8,moment8,map_add,clearMoment8Part0_eval h v z hh,clearMoment8Part1_eval h v z hh,clearMoment8Part2_eval h v z hh,clearMoment8Part3_eval h v z hh,clearMoment8Part4_eval h v z hh,clearMoment8Part5_eval h v z hh,clearMoment8Part6_eval h v z hh,clearMoment8Part7_eval h v z hh,clearMoment8Part8_eval h v z hh,clearMoment8Part9_eval h v z hh,clearMoment8Part10_eval h v z hh,clearMoment8Part11_eval h v z hh,clearMoment8Part12_eval h v z hh,clearMoment8Part13_eval h v z hh]
  ring

theorem clearMoment8_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 9 clearMoment8)=
      h^11*eval (basePoint v h⁻¹ z) (squareLie moment8) := by
  simp only [clearMoment8,clockFlow_add,map_add,clearMoment8Part0_flow h v z hh,clearMoment8Part1_flow h v z hh,clearMoment8Part2_flow h v z hh,clearMoment8Part3_flow h v z hh,clearMoment8Part4_flow h v z hh,clearMoment8Part5_flow h v z hh,clearMoment8Part6_flow h v z hh,clearMoment8Part7_flow h v z hh,clearMoment8Part8_flow h v z hh,clearMoment8Part9_flow h v z hh,clearMoment8Part10_flow h v z hh,clearMoment8Part11_flow h v z hh,clearMoment8Part12_flow h v z hh,clearMoment8Part13_flow h v z hh]
  simp only [moment8,squareLie,flow_add,map_add]
  ring

def clearMoment10 : Poly := ((((clearMoment10Part0 + clearMoment10Part1) + (clearMoment10Part2 + (clearMoment10Part3 + clearMoment10Part4))) + ((clearMoment10Part5 + (clearMoment10Part6 + clearMoment10Part7)) + (clearMoment10Part8 + (clearMoment10Part9 + clearMoment10Part10)))) + (((clearMoment10Part11 + (clearMoment10Part12 + clearMoment10Part13)) + (clearMoment10Part14 + (clearMoment10Part15 + clearMoment10Part16))) + ((clearMoment10Part17 + (clearMoment10Part18 + clearMoment10Part19)) + (clearMoment10Part20 + (clearMoment10Part21 + clearMoment10Part22)))))

theorem clearMoment10_eval (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) clearMoment10=h^11*eval (basePoint v h⁻¹ z) moment10 := by
  simp only [clearMoment10,moment10,map_add,clearMoment10Part0_eval h v z hh,clearMoment10Part1_eval h v z hh,clearMoment10Part2_eval h v z hh,clearMoment10Part3_eval h v z hh,clearMoment10Part4_eval h v z hh,clearMoment10Part5_eval h v z hh,clearMoment10Part6_eval h v z hh,clearMoment10Part7_eval h v z hh,clearMoment10Part8_eval h v z hh,clearMoment10Part9_eval h v z hh,clearMoment10Part10_eval h v z hh,clearMoment10Part11_eval h v z hh,clearMoment10Part12_eval h v z hh,clearMoment10Part13_eval h v z hh,clearMoment10Part14_eval h v z hh,clearMoment10Part15_eval h v z hh,clearMoment10Part16_eval h v z hh,clearMoment10Part17_eval h v z hh,clearMoment10Part18_eval h v z hh,clearMoment10Part19_eval h v z hh,clearMoment10Part20_eval h v z hh,clearMoment10Part21_eval h v z hh,clearMoment10Part22_eval h v z hh]
  ring

theorem clearMoment10_flow (h v z : ℂ) (hh : h≠0) :
    eval (basePoint h v z) (clockFlow 11 clearMoment10)=
      h^13*eval (basePoint v h⁻¹ z) (squareLie moment10) := by
  simp only [clearMoment10,clockFlow_add,map_add,clearMoment10Part0_flow h v z hh,clearMoment10Part1_flow h v z hh,clearMoment10Part2_flow h v z hh,clearMoment10Part3_flow h v z hh,clearMoment10Part4_flow h v z hh,clearMoment10Part5_flow h v z hh,clearMoment10Part6_flow h v z hh,clearMoment10Part7_flow h v z hh,clearMoment10Part8_flow h v z hh,clearMoment10Part9_flow h v z hh,clearMoment10Part10_flow h v z hh,clearMoment10Part11_flow h v z hh,clearMoment10Part12_flow h v z hh,clearMoment10Part13_flow h v z hh,clearMoment10Part14_flow h v z hh,clearMoment10Part15_flow h v z hh,clearMoment10Part16_flow h v z hh,clearMoment10Part17_flow h v z hh,clearMoment10Part18_flow h v z hh,clearMoment10Part19_flow h v z hh,clearMoment10Part20_flow h v z hh,clearMoment10Part21_flow h v z hh,clearMoment10Part22_flow h v z hh]
  simp only [moment10,squareLie,flow_add,map_add]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
