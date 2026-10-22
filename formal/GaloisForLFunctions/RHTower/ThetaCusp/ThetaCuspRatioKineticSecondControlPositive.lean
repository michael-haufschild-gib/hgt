import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorReconstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow0
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow7
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow9
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow11
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow12
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow13
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow14
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow15
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow16
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow17
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow18
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow19
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow20
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow21
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow22
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow23
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow24
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow25
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow26
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow27
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow28
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow29
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow30
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow31
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow32
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow33
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSecondTensorRow34
import Mathlib.Tactic.FinCases
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

theorem secondControlDefectTensorCoefficient_row0_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 0 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_0_0_pos
  · exact secondControlDefectTensorCoefficient_0_1_pos
  · exact secondControlDefectTensorCoefficient_0_2_pos
  · exact secondControlDefectTensorCoefficient_0_3_pos
  · exact secondControlDefectTensorCoefficient_0_4_pos
  · exact secondControlDefectTensorCoefficient_0_5_pos
  · exact secondControlDefectTensorCoefficient_0_6_pos
  · exact secondControlDefectTensorCoefficient_0_7_pos
  · exact secondControlDefectTensorCoefficient_0_8_pos
  · exact secondControlDefectTensorCoefficient_0_9_pos

theorem secondControlDefectTensorCoefficient_row1_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 1 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_1_0_pos
  · exact secondControlDefectTensorCoefficient_1_1_pos
  · exact secondControlDefectTensorCoefficient_1_2_pos
  · exact secondControlDefectTensorCoefficient_1_3_pos
  · exact secondControlDefectTensorCoefficient_1_4_pos
  · exact secondControlDefectTensorCoefficient_1_5_pos
  · exact secondControlDefectTensorCoefficient_1_6_pos
  · exact secondControlDefectTensorCoefficient_1_7_pos
  · exact secondControlDefectTensorCoefficient_1_8_pos
  · exact secondControlDefectTensorCoefficient_1_9_pos

theorem secondControlDefectTensorCoefficient_row2_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 2 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_2_0_pos
  · exact secondControlDefectTensorCoefficient_2_1_pos
  · exact secondControlDefectTensorCoefficient_2_2_pos
  · exact secondControlDefectTensorCoefficient_2_3_pos
  · exact secondControlDefectTensorCoefficient_2_4_pos
  · exact secondControlDefectTensorCoefficient_2_5_pos
  · exact secondControlDefectTensorCoefficient_2_6_pos
  · exact secondControlDefectTensorCoefficient_2_7_pos
  · exact secondControlDefectTensorCoefficient_2_8_pos
  · exact secondControlDefectTensorCoefficient_2_9_pos

theorem secondControlDefectTensorCoefficient_row3_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 3 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_3_0_pos
  · exact secondControlDefectTensorCoefficient_3_1_pos
  · exact secondControlDefectTensorCoefficient_3_2_pos
  · exact secondControlDefectTensorCoefficient_3_3_pos
  · exact secondControlDefectTensorCoefficient_3_4_pos
  · exact secondControlDefectTensorCoefficient_3_5_pos
  · exact secondControlDefectTensorCoefficient_3_6_pos
  · exact secondControlDefectTensorCoefficient_3_7_pos
  · exact secondControlDefectTensorCoefficient_3_8_pos
  · exact secondControlDefectTensorCoefficient_3_9_pos

theorem secondControlDefectTensorCoefficient_row4_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 4 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_4_0_pos
  · exact secondControlDefectTensorCoefficient_4_1_pos
  · exact secondControlDefectTensorCoefficient_4_2_pos
  · exact secondControlDefectTensorCoefficient_4_3_pos
  · exact secondControlDefectTensorCoefficient_4_4_pos
  · exact secondControlDefectTensorCoefficient_4_5_pos
  · exact secondControlDefectTensorCoefficient_4_6_pos
  · exact secondControlDefectTensorCoefficient_4_7_pos
  · exact secondControlDefectTensorCoefficient_4_8_pos
  · exact secondControlDefectTensorCoefficient_4_9_pos

theorem secondControlDefectTensorCoefficient_row5_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 5 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_5_0_pos
  · exact secondControlDefectTensorCoefficient_5_1_pos
  · exact secondControlDefectTensorCoefficient_5_2_pos
  · exact secondControlDefectTensorCoefficient_5_3_pos
  · exact secondControlDefectTensorCoefficient_5_4_pos
  · exact secondControlDefectTensorCoefficient_5_5_pos
  · exact secondControlDefectTensorCoefficient_5_6_pos
  · exact secondControlDefectTensorCoefficient_5_7_pos
  · exact secondControlDefectTensorCoefficient_5_8_pos
  · exact secondControlDefectTensorCoefficient_5_9_pos

theorem secondControlDefectTensorCoefficient_row6_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 6 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_6_0_pos
  · exact secondControlDefectTensorCoefficient_6_1_pos
  · exact secondControlDefectTensorCoefficient_6_2_pos
  · exact secondControlDefectTensorCoefficient_6_3_pos
  · exact secondControlDefectTensorCoefficient_6_4_pos
  · exact secondControlDefectTensorCoefficient_6_5_pos
  · exact secondControlDefectTensorCoefficient_6_6_pos
  · exact secondControlDefectTensorCoefficient_6_7_pos
  · exact secondControlDefectTensorCoefficient_6_8_pos
  · exact secondControlDefectTensorCoefficient_6_9_pos

theorem secondControlDefectTensorCoefficient_row7_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 7 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_7_0_pos
  · exact secondControlDefectTensorCoefficient_7_1_pos
  · exact secondControlDefectTensorCoefficient_7_2_pos
  · exact secondControlDefectTensorCoefficient_7_3_pos
  · exact secondControlDefectTensorCoefficient_7_4_pos
  · exact secondControlDefectTensorCoefficient_7_5_pos
  · exact secondControlDefectTensorCoefficient_7_6_pos
  · exact secondControlDefectTensorCoefficient_7_7_pos
  · exact secondControlDefectTensorCoefficient_7_8_pos
  · exact secondControlDefectTensorCoefficient_7_9_pos

theorem secondControlDefectTensorCoefficient_row8_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 8 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_8_0_pos
  · exact secondControlDefectTensorCoefficient_8_1_pos
  · exact secondControlDefectTensorCoefficient_8_2_pos
  · exact secondControlDefectTensorCoefficient_8_3_pos
  · exact secondControlDefectTensorCoefficient_8_4_pos
  · exact secondControlDefectTensorCoefficient_8_5_pos
  · exact secondControlDefectTensorCoefficient_8_6_pos
  · exact secondControlDefectTensorCoefficient_8_7_pos
  · exact secondControlDefectTensorCoefficient_8_8_pos
  · exact secondControlDefectTensorCoefficient_8_9_pos

theorem secondControlDefectTensorCoefficient_row9_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 9 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_9_0_pos
  · exact secondControlDefectTensorCoefficient_9_1_pos
  · exact secondControlDefectTensorCoefficient_9_2_pos
  · exact secondControlDefectTensorCoefficient_9_3_pos
  · exact secondControlDefectTensorCoefficient_9_4_pos
  · exact secondControlDefectTensorCoefficient_9_5_pos
  · exact secondControlDefectTensorCoefficient_9_6_pos
  · exact secondControlDefectTensorCoefficient_9_7_pos
  · exact secondControlDefectTensorCoefficient_9_8_pos
  · exact secondControlDefectTensorCoefficient_9_9_pos

theorem secondControlDefectTensorCoefficient_row10_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 10 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_10_0_pos
  · exact secondControlDefectTensorCoefficient_10_1_pos
  · exact secondControlDefectTensorCoefficient_10_2_pos
  · exact secondControlDefectTensorCoefficient_10_3_pos
  · exact secondControlDefectTensorCoefficient_10_4_pos
  · exact secondControlDefectTensorCoefficient_10_5_pos
  · exact secondControlDefectTensorCoefficient_10_6_pos
  · exact secondControlDefectTensorCoefficient_10_7_pos
  · exact secondControlDefectTensorCoefficient_10_8_pos
  · exact secondControlDefectTensorCoefficient_10_9_pos

theorem secondControlDefectTensorCoefficient_row11_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 11 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_11_0_pos
  · exact secondControlDefectTensorCoefficient_11_1_pos
  · exact secondControlDefectTensorCoefficient_11_2_pos
  · exact secondControlDefectTensorCoefficient_11_3_pos
  · exact secondControlDefectTensorCoefficient_11_4_pos
  · exact secondControlDefectTensorCoefficient_11_5_pos
  · exact secondControlDefectTensorCoefficient_11_6_pos
  · exact secondControlDefectTensorCoefficient_11_7_pos
  · exact secondControlDefectTensorCoefficient_11_8_pos
  · exact secondControlDefectTensorCoefficient_11_9_pos

theorem secondControlDefectTensorCoefficient_row12_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 12 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_12_0_pos
  · exact secondControlDefectTensorCoefficient_12_1_pos
  · exact secondControlDefectTensorCoefficient_12_2_pos
  · exact secondControlDefectTensorCoefficient_12_3_pos
  · exact secondControlDefectTensorCoefficient_12_4_pos
  · exact secondControlDefectTensorCoefficient_12_5_pos
  · exact secondControlDefectTensorCoefficient_12_6_pos
  · exact secondControlDefectTensorCoefficient_12_7_pos
  · exact secondControlDefectTensorCoefficient_12_8_pos
  · exact secondControlDefectTensorCoefficient_12_9_pos

theorem secondControlDefectTensorCoefficient_row13_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 13 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_13_0_pos
  · exact secondControlDefectTensorCoefficient_13_1_pos
  · exact secondControlDefectTensorCoefficient_13_2_pos
  · exact secondControlDefectTensorCoefficient_13_3_pos
  · exact secondControlDefectTensorCoefficient_13_4_pos
  · exact secondControlDefectTensorCoefficient_13_5_pos
  · exact secondControlDefectTensorCoefficient_13_6_pos
  · exact secondControlDefectTensorCoefficient_13_7_pos
  · exact secondControlDefectTensorCoefficient_13_8_pos
  · exact secondControlDefectTensorCoefficient_13_9_pos

theorem secondControlDefectTensorCoefficient_row14_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 14 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_14_0_pos
  · exact secondControlDefectTensorCoefficient_14_1_pos
  · exact secondControlDefectTensorCoefficient_14_2_pos
  · exact secondControlDefectTensorCoefficient_14_3_pos
  · exact secondControlDefectTensorCoefficient_14_4_pos
  · exact secondControlDefectTensorCoefficient_14_5_pos
  · exact secondControlDefectTensorCoefficient_14_6_pos
  · exact secondControlDefectTensorCoefficient_14_7_pos
  · exact secondControlDefectTensorCoefficient_14_8_pos
  · exact secondControlDefectTensorCoefficient_14_9_pos

theorem secondControlDefectTensorCoefficient_row15_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 15 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_15_0_pos
  · exact secondControlDefectTensorCoefficient_15_1_pos
  · exact secondControlDefectTensorCoefficient_15_2_pos
  · exact secondControlDefectTensorCoefficient_15_3_pos
  · exact secondControlDefectTensorCoefficient_15_4_pos
  · exact secondControlDefectTensorCoefficient_15_5_pos
  · exact secondControlDefectTensorCoefficient_15_6_pos
  · exact secondControlDefectTensorCoefficient_15_7_pos
  · exact secondControlDefectTensorCoefficient_15_8_pos
  · exact secondControlDefectTensorCoefficient_15_9_pos

theorem secondControlDefectTensorCoefficient_row16_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 16 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_16_0_pos
  · exact secondControlDefectTensorCoefficient_16_1_pos
  · exact secondControlDefectTensorCoefficient_16_2_pos
  · exact secondControlDefectTensorCoefficient_16_3_pos
  · exact secondControlDefectTensorCoefficient_16_4_pos
  · exact secondControlDefectTensorCoefficient_16_5_pos
  · exact secondControlDefectTensorCoefficient_16_6_pos
  · exact secondControlDefectTensorCoefficient_16_7_pos
  · exact secondControlDefectTensorCoefficient_16_8_pos
  · exact secondControlDefectTensorCoefficient_16_9_pos

theorem secondControlDefectTensorCoefficient_row17_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 17 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_17_0_pos
  · exact secondControlDefectTensorCoefficient_17_1_pos
  · exact secondControlDefectTensorCoefficient_17_2_pos
  · exact secondControlDefectTensorCoefficient_17_3_pos
  · exact secondControlDefectTensorCoefficient_17_4_pos
  · exact secondControlDefectTensorCoefficient_17_5_pos
  · exact secondControlDefectTensorCoefficient_17_6_pos
  · exact secondControlDefectTensorCoefficient_17_7_pos
  · exact secondControlDefectTensorCoefficient_17_8_pos
  · exact secondControlDefectTensorCoefficient_17_9_pos

theorem secondControlDefectTensorCoefficient_row18_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 18 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_18_0_pos
  · exact secondControlDefectTensorCoefficient_18_1_pos
  · exact secondControlDefectTensorCoefficient_18_2_pos
  · exact secondControlDefectTensorCoefficient_18_3_pos
  · exact secondControlDefectTensorCoefficient_18_4_pos
  · exact secondControlDefectTensorCoefficient_18_5_pos
  · exact secondControlDefectTensorCoefficient_18_6_pos
  · exact secondControlDefectTensorCoefficient_18_7_pos
  · exact secondControlDefectTensorCoefficient_18_8_pos
  · exact secondControlDefectTensorCoefficient_18_9_pos

theorem secondControlDefectTensorCoefficient_row19_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 19 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_19_0_pos
  · exact secondControlDefectTensorCoefficient_19_1_pos
  · exact secondControlDefectTensorCoefficient_19_2_pos
  · exact secondControlDefectTensorCoefficient_19_3_pos
  · exact secondControlDefectTensorCoefficient_19_4_pos
  · exact secondControlDefectTensorCoefficient_19_5_pos
  · exact secondControlDefectTensorCoefficient_19_6_pos
  · exact secondControlDefectTensorCoefficient_19_7_pos
  · exact secondControlDefectTensorCoefficient_19_8_pos
  · exact secondControlDefectTensorCoefficient_19_9_pos

theorem secondControlDefectTensorCoefficient_row20_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 20 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_20_0_pos
  · exact secondControlDefectTensorCoefficient_20_1_pos
  · exact secondControlDefectTensorCoefficient_20_2_pos
  · exact secondControlDefectTensorCoefficient_20_3_pos
  · exact secondControlDefectTensorCoefficient_20_4_pos
  · exact secondControlDefectTensorCoefficient_20_5_pos
  · exact secondControlDefectTensorCoefficient_20_6_pos
  · exact secondControlDefectTensorCoefficient_20_7_pos
  · exact secondControlDefectTensorCoefficient_20_8_pos
  · exact secondControlDefectTensorCoefficient_20_9_pos

theorem secondControlDefectTensorCoefficient_row21_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 21 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_21_0_pos
  · exact secondControlDefectTensorCoefficient_21_1_pos
  · exact secondControlDefectTensorCoefficient_21_2_pos
  · exact secondControlDefectTensorCoefficient_21_3_pos
  · exact secondControlDefectTensorCoefficient_21_4_pos
  · exact secondControlDefectTensorCoefficient_21_5_pos
  · exact secondControlDefectTensorCoefficient_21_6_pos
  · exact secondControlDefectTensorCoefficient_21_7_pos
  · exact secondControlDefectTensorCoefficient_21_8_pos
  · exact secondControlDefectTensorCoefficient_21_9_pos

theorem secondControlDefectTensorCoefficient_row22_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 22 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_22_0_pos
  · exact secondControlDefectTensorCoefficient_22_1_pos
  · exact secondControlDefectTensorCoefficient_22_2_pos
  · exact secondControlDefectTensorCoefficient_22_3_pos
  · exact secondControlDefectTensorCoefficient_22_4_pos
  · exact secondControlDefectTensorCoefficient_22_5_pos
  · exact secondControlDefectTensorCoefficient_22_6_pos
  · exact secondControlDefectTensorCoefficient_22_7_pos
  · exact secondControlDefectTensorCoefficient_22_8_pos
  · exact secondControlDefectTensorCoefficient_22_9_pos

theorem secondControlDefectTensorCoefficient_row23_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 23 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_23_0_pos
  · exact secondControlDefectTensorCoefficient_23_1_pos
  · exact secondControlDefectTensorCoefficient_23_2_pos
  · exact secondControlDefectTensorCoefficient_23_3_pos
  · exact secondControlDefectTensorCoefficient_23_4_pos
  · exact secondControlDefectTensorCoefficient_23_5_pos
  · exact secondControlDefectTensorCoefficient_23_6_pos
  · exact secondControlDefectTensorCoefficient_23_7_pos
  · exact secondControlDefectTensorCoefficient_23_8_pos
  · exact secondControlDefectTensorCoefficient_23_9_pos

theorem secondControlDefectTensorCoefficient_row24_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 24 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_24_0_pos
  · exact secondControlDefectTensorCoefficient_24_1_pos
  · exact secondControlDefectTensorCoefficient_24_2_pos
  · exact secondControlDefectTensorCoefficient_24_3_pos
  · exact secondControlDefectTensorCoefficient_24_4_pos
  · exact secondControlDefectTensorCoefficient_24_5_pos
  · exact secondControlDefectTensorCoefficient_24_6_pos
  · exact secondControlDefectTensorCoefficient_24_7_pos
  · exact secondControlDefectTensorCoefficient_24_8_pos
  · exact secondControlDefectTensorCoefficient_24_9_pos

theorem secondControlDefectTensorCoefficient_row25_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 25 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_25_0_pos
  · exact secondControlDefectTensorCoefficient_25_1_pos
  · exact secondControlDefectTensorCoefficient_25_2_pos
  · exact secondControlDefectTensorCoefficient_25_3_pos
  · exact secondControlDefectTensorCoefficient_25_4_pos
  · exact secondControlDefectTensorCoefficient_25_5_pos
  · exact secondControlDefectTensorCoefficient_25_6_pos
  · exact secondControlDefectTensorCoefficient_25_7_pos
  · exact secondControlDefectTensorCoefficient_25_8_pos
  · exact secondControlDefectTensorCoefficient_25_9_pos

theorem secondControlDefectTensorCoefficient_row26_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 26 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_26_0_pos
  · exact secondControlDefectTensorCoefficient_26_1_pos
  · exact secondControlDefectTensorCoefficient_26_2_pos
  · exact secondControlDefectTensorCoefficient_26_3_pos
  · exact secondControlDefectTensorCoefficient_26_4_pos
  · exact secondControlDefectTensorCoefficient_26_5_pos
  · exact secondControlDefectTensorCoefficient_26_6_pos
  · exact secondControlDefectTensorCoefficient_26_7_pos
  · exact secondControlDefectTensorCoefficient_26_8_pos
  · exact secondControlDefectTensorCoefficient_26_9_pos

theorem secondControlDefectTensorCoefficient_row27_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 27 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_27_0_pos
  · exact secondControlDefectTensorCoefficient_27_1_pos
  · exact secondControlDefectTensorCoefficient_27_2_pos
  · exact secondControlDefectTensorCoefficient_27_3_pos
  · exact secondControlDefectTensorCoefficient_27_4_pos
  · exact secondControlDefectTensorCoefficient_27_5_pos
  · exact secondControlDefectTensorCoefficient_27_6_pos
  · exact secondControlDefectTensorCoefficient_27_7_pos
  · exact secondControlDefectTensorCoefficient_27_8_pos
  · exact secondControlDefectTensorCoefficient_27_9_pos

theorem secondControlDefectTensorCoefficient_row28_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 28 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_28_0_pos
  · exact secondControlDefectTensorCoefficient_28_1_pos
  · exact secondControlDefectTensorCoefficient_28_2_pos
  · exact secondControlDefectTensorCoefficient_28_3_pos
  · exact secondControlDefectTensorCoefficient_28_4_pos
  · exact secondControlDefectTensorCoefficient_28_5_pos
  · exact secondControlDefectTensorCoefficient_28_6_pos
  · exact secondControlDefectTensorCoefficient_28_7_pos
  · exact secondControlDefectTensorCoefficient_28_8_pos
  · exact secondControlDefectTensorCoefficient_28_9_pos

theorem secondControlDefectTensorCoefficient_row29_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 29 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_29_0_pos
  · exact secondControlDefectTensorCoefficient_29_1_pos
  · exact secondControlDefectTensorCoefficient_29_2_pos
  · exact secondControlDefectTensorCoefficient_29_3_pos
  · exact secondControlDefectTensorCoefficient_29_4_pos
  · exact secondControlDefectTensorCoefficient_29_5_pos
  · exact secondControlDefectTensorCoefficient_29_6_pos
  · exact secondControlDefectTensorCoefficient_29_7_pos
  · exact secondControlDefectTensorCoefficient_29_8_pos
  · exact secondControlDefectTensorCoefficient_29_9_pos

theorem secondControlDefectTensorCoefficient_row30_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 30 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_30_0_pos
  · exact secondControlDefectTensorCoefficient_30_1_pos
  · exact secondControlDefectTensorCoefficient_30_2_pos
  · exact secondControlDefectTensorCoefficient_30_3_pos
  · exact secondControlDefectTensorCoefficient_30_4_pos
  · exact secondControlDefectTensorCoefficient_30_5_pos
  · exact secondControlDefectTensorCoefficient_30_6_pos
  · exact secondControlDefectTensorCoefficient_30_7_pos
  · exact secondControlDefectTensorCoefficient_30_8_pos
  · exact secondControlDefectTensorCoefficient_30_9_pos

theorem secondControlDefectTensorCoefficient_row31_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 31 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_31_0_pos
  · exact secondControlDefectTensorCoefficient_31_1_pos
  · exact secondControlDefectTensorCoefficient_31_2_pos
  · exact secondControlDefectTensorCoefficient_31_3_pos
  · exact secondControlDefectTensorCoefficient_31_4_pos
  · exact secondControlDefectTensorCoefficient_31_5_pos
  · exact secondControlDefectTensorCoefficient_31_6_pos
  · exact secondControlDefectTensorCoefficient_31_7_pos
  · exact secondControlDefectTensorCoefficient_31_8_pos
  · exact secondControlDefectTensorCoefficient_31_9_pos

theorem secondControlDefectTensorCoefficient_row32_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 32 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_32_0_pos
  · exact secondControlDefectTensorCoefficient_32_1_pos
  · exact secondControlDefectTensorCoefficient_32_2_pos
  · exact secondControlDefectTensorCoefficient_32_3_pos
  · exact secondControlDefectTensorCoefficient_32_4_pos
  · exact secondControlDefectTensorCoefficient_32_5_pos
  · exact secondControlDefectTensorCoefficient_32_6_pos
  · exact secondControlDefectTensorCoefficient_32_7_pos
  · exact secondControlDefectTensorCoefficient_32_8_pos
  · exact secondControlDefectTensorCoefficient_32_9_pos

theorem secondControlDefectTensorCoefficient_row33_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 33 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_33_0_pos
  · exact secondControlDefectTensorCoefficient_33_1_pos
  · exact secondControlDefectTensorCoefficient_33_2_pos
  · exact secondControlDefectTensorCoefficient_33_3_pos
  · exact secondControlDefectTensorCoefficient_33_4_pos
  · exact secondControlDefectTensorCoefficient_33_5_pos
  · exact secondControlDefectTensorCoefficient_33_6_pos
  · exact secondControlDefectTensorCoefficient_33_7_pos
  · exact secondControlDefectTensorCoefficient_33_8_pos
  · exact secondControlDefectTensorCoefficient_33_9_pos

theorem secondControlDefectTensorCoefficient_row34_pos (B : Fin 10) :
    0<secondControlDefectTensorCoefficient 34 B := by
  fin_cases B
  · exact secondControlDefectTensorCoefficient_34_0_pos
  · exact secondControlDefectTensorCoefficient_34_1_pos
  · exact secondControlDefectTensorCoefficient_34_2_pos
  · exact secondControlDefectTensorCoefficient_34_3_pos
  · exact secondControlDefectTensorCoefficient_34_4_pos
  · exact secondControlDefectTensorCoefficient_34_5_pos
  · exact secondControlDefectTensorCoefficient_34_6_pos
  · exact secondControlDefectTensorCoefficient_34_7_pos
  · exact secondControlDefectTensorCoefficient_34_8_pos
  · exact secondControlDefectTensorCoefficient_34_9_pos

theorem secondControlDefectTensorCoefficient_pos (A : Fin 35) (B : Fin 10) :
    0<secondControlDefectTensorCoefficient A B := by
  fin_cases A
  · exact secondControlDefectTensorCoefficient_row0_pos B
  · exact secondControlDefectTensorCoefficient_row1_pos B
  · exact secondControlDefectTensorCoefficient_row2_pos B
  · exact secondControlDefectTensorCoefficient_row3_pos B
  · exact secondControlDefectTensorCoefficient_row4_pos B
  · exact secondControlDefectTensorCoefficient_row5_pos B
  · exact secondControlDefectTensorCoefficient_row6_pos B
  · exact secondControlDefectTensorCoefficient_row7_pos B
  · exact secondControlDefectTensorCoefficient_row8_pos B
  · exact secondControlDefectTensorCoefficient_row9_pos B
  · exact secondControlDefectTensorCoefficient_row10_pos B
  · exact secondControlDefectTensorCoefficient_row11_pos B
  · exact secondControlDefectTensorCoefficient_row12_pos B
  · exact secondControlDefectTensorCoefficient_row13_pos B
  · exact secondControlDefectTensorCoefficient_row14_pos B
  · exact secondControlDefectTensorCoefficient_row15_pos B
  · exact secondControlDefectTensorCoefficient_row16_pos B
  · exact secondControlDefectTensorCoefficient_row17_pos B
  · exact secondControlDefectTensorCoefficient_row18_pos B
  · exact secondControlDefectTensorCoefficient_row19_pos B
  · exact secondControlDefectTensorCoefficient_row20_pos B
  · exact secondControlDefectTensorCoefficient_row21_pos B
  · exact secondControlDefectTensorCoefficient_row22_pos B
  · exact secondControlDefectTensorCoefficient_row23_pos B
  · exact secondControlDefectTensorCoefficient_row24_pos B
  · exact secondControlDefectTensorCoefficient_row25_pos B
  · exact secondControlDefectTensorCoefficient_row26_pos B
  · exact secondControlDefectTensorCoefficient_row27_pos B
  · exact secondControlDefectTensorCoefficient_row28_pos B
  · exact secondControlDefectTensorCoefficient_row29_pos B
  · exact secondControlDefectTensorCoefficient_row30_pos B
  · exact secondControlDefectTensorCoefficient_row31_pos B
  · exact secondControlDefectTensorCoefficient_row32_pos B
  · exact secondControlDefectTensorCoefficient_row33_pos B
  · exact secondControlDefectTensorCoefficient_row34_pos B

theorem secondControlDefectQuotient_unit_pos (t v : ℝ)
    (ht0 : 0≤t) (ht1 : t≤1) (hv0 : 0≤v) (hv1 : v≤1) :
    0<secondControlDefectQuotient ((4/5)*t) ((361/25)*v) := by
  rw [←secondControlDefectTensorValue_reconstruction]
  apply kineticBernstein_pos 34 _ t _ ht0 ht1
  intro A hA
  apply kineticBernstein_pos 9 _ v _ hv0 hv1
  intro B hB
  exact secondControlDefectTensorCoefficient_pos ⟨A,hA⟩ ⟨B,hB⟩

theorem secondControlDefectQuotient_pos (h r : ℝ)
    (hh0 : 0≤h) (hh1 : h≤4/5) (hr0 : 0≤r) (hr1 : r≤361/25) :
    0<secondControlDefectQuotient h r := by
  have ht0 : 0≤h/(4/5:ℝ) := div_nonneg hh0 (by norm_num)
  have ht1 : h/(4/5:ℝ)≤1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hh1)
  have hv0 : 0≤r/(361/25:ℝ) := div_nonneg hr0 (by norm_num)
  have hv1 : r/(361/25:ℝ)≤1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hr1)
  have hp := secondControlDefectQuotient_unit_pos (h/(4/5)) (r/(361/25)) ht0 ht1 hv0 hv1
  have he : (4/5:ℝ)*(h/(4/5))=h := by ring
  have re : (361/25:ℝ)*(r/(361/25))=r := by ring
  simpa only [he,re] using hp

theorem reducedKineticControl_one_third_pos (h r : ℝ)
    (hh0 : 0<h) (hh1 : h≤4/5) (hr0 : 0≤r) (hr1 : r≤361/25) :
    0<reducedKineticControl h (9-r*h^2) (1/3) 1 := by
  rw [secondControl_defect_factor]
  exact mul_pos (pow_pos hh0 _) (secondControlDefectQuotient_pos h r hh0.le hh1 hr0 hr1)

theorem reducedKineticControl_one_pos (h r Z : ℝ)
    (hh0 : 0<h) (hh1 : h≤4/5) (hr0 : 0≤r) (hr1 : r≤361/25)
    (hZ0 : 0≤Z) (hZ1 : Z≤1/3) :
    0<reducedKineticControl h (9-r*h^2) Z 1 := by
  have hZ : Z=(3*Z)*(1/3) := by ring
  rw [hZ,reducedKineticControl_contraction h (9-r*h^2) (1/3) (3*Z) 1 (by norm_num)]
  apply kineticBernstein_pos 1 _ (3*Z) _ (by positivity) (by linarith)
  intro i hi
  have hik : i=0 ∨ i=1 := by omega
  rcases hik with rfl | rfl
  · simpa [degreeElevationCoefficient] using mul_pos
      (reducedKineticControl_zero_pos h r (1/3) hh0 hh1 hr0 hr1)
      (show (0:ℝ)<19 by norm_num)
  · simpa [degreeElevationCoefficient] using reducedKineticControl_one_third_pos h r hh0 hh1 hr0 hr1

end
end HTGeometry.ThetaRatioKineticContraction
