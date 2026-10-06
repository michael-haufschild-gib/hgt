import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorReconstruction
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow0
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow1
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow3
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow4
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow5
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow7
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow9
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow10
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow11
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow12
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow13
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow14
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow15
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow16
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow17
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow18
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow19
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow20
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow21
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow22
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow23
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow24
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow25
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow26
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow27
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow28
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow29
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow30
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow31
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticFirstTensorRow32
import Mathlib.Tactic.FinCases
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

theorem firstControlDefectTensorCoefficient_row0_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 0 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_0_0_pos
  · exact firstControlDefectTensorCoefficient_0_1_pos
  · exact firstControlDefectTensorCoefficient_0_2_pos
  · exact firstControlDefectTensorCoefficient_0_3_pos
  · exact firstControlDefectTensorCoefficient_0_4_pos
  · exact firstControlDefectTensorCoefficient_0_5_pos
  · exact firstControlDefectTensorCoefficient_0_6_pos
  · exact firstControlDefectTensorCoefficient_0_7_pos
  · exact firstControlDefectTensorCoefficient_0_8_pos
  · exact firstControlDefectTensorCoefficient_0_9_pos

theorem firstControlDefectTensorCoefficient_row1_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 1 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_1_0_pos
  · exact firstControlDefectTensorCoefficient_1_1_pos
  · exact firstControlDefectTensorCoefficient_1_2_pos
  · exact firstControlDefectTensorCoefficient_1_3_pos
  · exact firstControlDefectTensorCoefficient_1_4_pos
  · exact firstControlDefectTensorCoefficient_1_5_pos
  · exact firstControlDefectTensorCoefficient_1_6_pos
  · exact firstControlDefectTensorCoefficient_1_7_pos
  · exact firstControlDefectTensorCoefficient_1_8_pos
  · exact firstControlDefectTensorCoefficient_1_9_pos

theorem firstControlDefectTensorCoefficient_row2_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 2 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_2_0_pos
  · exact firstControlDefectTensorCoefficient_2_1_pos
  · exact firstControlDefectTensorCoefficient_2_2_pos
  · exact firstControlDefectTensorCoefficient_2_3_pos
  · exact firstControlDefectTensorCoefficient_2_4_pos
  · exact firstControlDefectTensorCoefficient_2_5_pos
  · exact firstControlDefectTensorCoefficient_2_6_pos
  · exact firstControlDefectTensorCoefficient_2_7_pos
  · exact firstControlDefectTensorCoefficient_2_8_pos
  · exact firstControlDefectTensorCoefficient_2_9_pos

theorem firstControlDefectTensorCoefficient_row3_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 3 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_3_0_pos
  · exact firstControlDefectTensorCoefficient_3_1_pos
  · exact firstControlDefectTensorCoefficient_3_2_pos
  · exact firstControlDefectTensorCoefficient_3_3_pos
  · exact firstControlDefectTensorCoefficient_3_4_pos
  · exact firstControlDefectTensorCoefficient_3_5_pos
  · exact firstControlDefectTensorCoefficient_3_6_pos
  · exact firstControlDefectTensorCoefficient_3_7_pos
  · exact firstControlDefectTensorCoefficient_3_8_pos
  · exact firstControlDefectTensorCoefficient_3_9_pos

theorem firstControlDefectTensorCoefficient_row4_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 4 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_4_0_pos
  · exact firstControlDefectTensorCoefficient_4_1_pos
  · exact firstControlDefectTensorCoefficient_4_2_pos
  · exact firstControlDefectTensorCoefficient_4_3_pos
  · exact firstControlDefectTensorCoefficient_4_4_pos
  · exact firstControlDefectTensorCoefficient_4_5_pos
  · exact firstControlDefectTensorCoefficient_4_6_pos
  · exact firstControlDefectTensorCoefficient_4_7_pos
  · exact firstControlDefectTensorCoefficient_4_8_pos
  · exact firstControlDefectTensorCoefficient_4_9_pos

theorem firstControlDefectTensorCoefficient_row5_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 5 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_5_0_pos
  · exact firstControlDefectTensorCoefficient_5_1_pos
  · exact firstControlDefectTensorCoefficient_5_2_pos
  · exact firstControlDefectTensorCoefficient_5_3_pos
  · exact firstControlDefectTensorCoefficient_5_4_pos
  · exact firstControlDefectTensorCoefficient_5_5_pos
  · exact firstControlDefectTensorCoefficient_5_6_pos
  · exact firstControlDefectTensorCoefficient_5_7_pos
  · exact firstControlDefectTensorCoefficient_5_8_pos
  · exact firstControlDefectTensorCoefficient_5_9_pos

theorem firstControlDefectTensorCoefficient_row6_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 6 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_6_0_pos
  · exact firstControlDefectTensorCoefficient_6_1_pos
  · exact firstControlDefectTensorCoefficient_6_2_pos
  · exact firstControlDefectTensorCoefficient_6_3_pos
  · exact firstControlDefectTensorCoefficient_6_4_pos
  · exact firstControlDefectTensorCoefficient_6_5_pos
  · exact firstControlDefectTensorCoefficient_6_6_pos
  · exact firstControlDefectTensorCoefficient_6_7_pos
  · exact firstControlDefectTensorCoefficient_6_8_pos
  · exact firstControlDefectTensorCoefficient_6_9_pos

theorem firstControlDefectTensorCoefficient_row7_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 7 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_7_0_pos
  · exact firstControlDefectTensorCoefficient_7_1_pos
  · exact firstControlDefectTensorCoefficient_7_2_pos
  · exact firstControlDefectTensorCoefficient_7_3_pos
  · exact firstControlDefectTensorCoefficient_7_4_pos
  · exact firstControlDefectTensorCoefficient_7_5_pos
  · exact firstControlDefectTensorCoefficient_7_6_pos
  · exact firstControlDefectTensorCoefficient_7_7_pos
  · exact firstControlDefectTensorCoefficient_7_8_pos
  · exact firstControlDefectTensorCoefficient_7_9_pos

theorem firstControlDefectTensorCoefficient_row8_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 8 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_8_0_pos
  · exact firstControlDefectTensorCoefficient_8_1_pos
  · exact firstControlDefectTensorCoefficient_8_2_pos
  · exact firstControlDefectTensorCoefficient_8_3_pos
  · exact firstControlDefectTensorCoefficient_8_4_pos
  · exact firstControlDefectTensorCoefficient_8_5_pos
  · exact firstControlDefectTensorCoefficient_8_6_pos
  · exact firstControlDefectTensorCoefficient_8_7_pos
  · exact firstControlDefectTensorCoefficient_8_8_pos
  · exact firstControlDefectTensorCoefficient_8_9_pos

theorem firstControlDefectTensorCoefficient_row9_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 9 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_9_0_pos
  · exact firstControlDefectTensorCoefficient_9_1_pos
  · exact firstControlDefectTensorCoefficient_9_2_pos
  · exact firstControlDefectTensorCoefficient_9_3_pos
  · exact firstControlDefectTensorCoefficient_9_4_pos
  · exact firstControlDefectTensorCoefficient_9_5_pos
  · exact firstControlDefectTensorCoefficient_9_6_pos
  · exact firstControlDefectTensorCoefficient_9_7_pos
  · exact firstControlDefectTensorCoefficient_9_8_pos
  · exact firstControlDefectTensorCoefficient_9_9_pos

theorem firstControlDefectTensorCoefficient_row10_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 10 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_10_0_pos
  · exact firstControlDefectTensorCoefficient_10_1_pos
  · exact firstControlDefectTensorCoefficient_10_2_pos
  · exact firstControlDefectTensorCoefficient_10_3_pos
  · exact firstControlDefectTensorCoefficient_10_4_pos
  · exact firstControlDefectTensorCoefficient_10_5_pos
  · exact firstControlDefectTensorCoefficient_10_6_pos
  · exact firstControlDefectTensorCoefficient_10_7_pos
  · exact firstControlDefectTensorCoefficient_10_8_pos
  · exact firstControlDefectTensorCoefficient_10_9_pos

theorem firstControlDefectTensorCoefficient_row11_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 11 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_11_0_pos
  · exact firstControlDefectTensorCoefficient_11_1_pos
  · exact firstControlDefectTensorCoefficient_11_2_pos
  · exact firstControlDefectTensorCoefficient_11_3_pos
  · exact firstControlDefectTensorCoefficient_11_4_pos
  · exact firstControlDefectTensorCoefficient_11_5_pos
  · exact firstControlDefectTensorCoefficient_11_6_pos
  · exact firstControlDefectTensorCoefficient_11_7_pos
  · exact firstControlDefectTensorCoefficient_11_8_pos
  · exact firstControlDefectTensorCoefficient_11_9_pos

theorem firstControlDefectTensorCoefficient_row12_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 12 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_12_0_pos
  · exact firstControlDefectTensorCoefficient_12_1_pos
  · exact firstControlDefectTensorCoefficient_12_2_pos
  · exact firstControlDefectTensorCoefficient_12_3_pos
  · exact firstControlDefectTensorCoefficient_12_4_pos
  · exact firstControlDefectTensorCoefficient_12_5_pos
  · exact firstControlDefectTensorCoefficient_12_6_pos
  · exact firstControlDefectTensorCoefficient_12_7_pos
  · exact firstControlDefectTensorCoefficient_12_8_pos
  · exact firstControlDefectTensorCoefficient_12_9_pos

theorem firstControlDefectTensorCoefficient_row13_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 13 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_13_0_pos
  · exact firstControlDefectTensorCoefficient_13_1_pos
  · exact firstControlDefectTensorCoefficient_13_2_pos
  · exact firstControlDefectTensorCoefficient_13_3_pos
  · exact firstControlDefectTensorCoefficient_13_4_pos
  · exact firstControlDefectTensorCoefficient_13_5_pos
  · exact firstControlDefectTensorCoefficient_13_6_pos
  · exact firstControlDefectTensorCoefficient_13_7_pos
  · exact firstControlDefectTensorCoefficient_13_8_pos
  · exact firstControlDefectTensorCoefficient_13_9_pos

theorem firstControlDefectTensorCoefficient_row14_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 14 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_14_0_pos
  · exact firstControlDefectTensorCoefficient_14_1_pos
  · exact firstControlDefectTensorCoefficient_14_2_pos
  · exact firstControlDefectTensorCoefficient_14_3_pos
  · exact firstControlDefectTensorCoefficient_14_4_pos
  · exact firstControlDefectTensorCoefficient_14_5_pos
  · exact firstControlDefectTensorCoefficient_14_6_pos
  · exact firstControlDefectTensorCoefficient_14_7_pos
  · exact firstControlDefectTensorCoefficient_14_8_pos
  · exact firstControlDefectTensorCoefficient_14_9_pos

theorem firstControlDefectTensorCoefficient_row15_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 15 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_15_0_pos
  · exact firstControlDefectTensorCoefficient_15_1_pos
  · exact firstControlDefectTensorCoefficient_15_2_pos
  · exact firstControlDefectTensorCoefficient_15_3_pos
  · exact firstControlDefectTensorCoefficient_15_4_pos
  · exact firstControlDefectTensorCoefficient_15_5_pos
  · exact firstControlDefectTensorCoefficient_15_6_pos
  · exact firstControlDefectTensorCoefficient_15_7_pos
  · exact firstControlDefectTensorCoefficient_15_8_pos
  · exact firstControlDefectTensorCoefficient_15_9_pos

theorem firstControlDefectTensorCoefficient_row16_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 16 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_16_0_pos
  · exact firstControlDefectTensorCoefficient_16_1_pos
  · exact firstControlDefectTensorCoefficient_16_2_pos
  · exact firstControlDefectTensorCoefficient_16_3_pos
  · exact firstControlDefectTensorCoefficient_16_4_pos
  · exact firstControlDefectTensorCoefficient_16_5_pos
  · exact firstControlDefectTensorCoefficient_16_6_pos
  · exact firstControlDefectTensorCoefficient_16_7_pos
  · exact firstControlDefectTensorCoefficient_16_8_pos
  · exact firstControlDefectTensorCoefficient_16_9_pos

theorem firstControlDefectTensorCoefficient_row17_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 17 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_17_0_pos
  · exact firstControlDefectTensorCoefficient_17_1_pos
  · exact firstControlDefectTensorCoefficient_17_2_pos
  · exact firstControlDefectTensorCoefficient_17_3_pos
  · exact firstControlDefectTensorCoefficient_17_4_pos
  · exact firstControlDefectTensorCoefficient_17_5_pos
  · exact firstControlDefectTensorCoefficient_17_6_pos
  · exact firstControlDefectTensorCoefficient_17_7_pos
  · exact firstControlDefectTensorCoefficient_17_8_pos
  · exact firstControlDefectTensorCoefficient_17_9_pos

theorem firstControlDefectTensorCoefficient_row18_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 18 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_18_0_pos
  · exact firstControlDefectTensorCoefficient_18_1_pos
  · exact firstControlDefectTensorCoefficient_18_2_pos
  · exact firstControlDefectTensorCoefficient_18_3_pos
  · exact firstControlDefectTensorCoefficient_18_4_pos
  · exact firstControlDefectTensorCoefficient_18_5_pos
  · exact firstControlDefectTensorCoefficient_18_6_pos
  · exact firstControlDefectTensorCoefficient_18_7_pos
  · exact firstControlDefectTensorCoefficient_18_8_pos
  · exact firstControlDefectTensorCoefficient_18_9_pos

theorem firstControlDefectTensorCoefficient_row19_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 19 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_19_0_pos
  · exact firstControlDefectTensorCoefficient_19_1_pos
  · exact firstControlDefectTensorCoefficient_19_2_pos
  · exact firstControlDefectTensorCoefficient_19_3_pos
  · exact firstControlDefectTensorCoefficient_19_4_pos
  · exact firstControlDefectTensorCoefficient_19_5_pos
  · exact firstControlDefectTensorCoefficient_19_6_pos
  · exact firstControlDefectTensorCoefficient_19_7_pos
  · exact firstControlDefectTensorCoefficient_19_8_pos
  · exact firstControlDefectTensorCoefficient_19_9_pos

theorem firstControlDefectTensorCoefficient_row20_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 20 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_20_0_pos
  · exact firstControlDefectTensorCoefficient_20_1_pos
  · exact firstControlDefectTensorCoefficient_20_2_pos
  · exact firstControlDefectTensorCoefficient_20_3_pos
  · exact firstControlDefectTensorCoefficient_20_4_pos
  · exact firstControlDefectTensorCoefficient_20_5_pos
  · exact firstControlDefectTensorCoefficient_20_6_pos
  · exact firstControlDefectTensorCoefficient_20_7_pos
  · exact firstControlDefectTensorCoefficient_20_8_pos
  · exact firstControlDefectTensorCoefficient_20_9_pos

theorem firstControlDefectTensorCoefficient_row21_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 21 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_21_0_pos
  · exact firstControlDefectTensorCoefficient_21_1_pos
  · exact firstControlDefectTensorCoefficient_21_2_pos
  · exact firstControlDefectTensorCoefficient_21_3_pos
  · exact firstControlDefectTensorCoefficient_21_4_pos
  · exact firstControlDefectTensorCoefficient_21_5_pos
  · exact firstControlDefectTensorCoefficient_21_6_pos
  · exact firstControlDefectTensorCoefficient_21_7_pos
  · exact firstControlDefectTensorCoefficient_21_8_pos
  · exact firstControlDefectTensorCoefficient_21_9_pos

theorem firstControlDefectTensorCoefficient_row22_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 22 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_22_0_pos
  · exact firstControlDefectTensorCoefficient_22_1_pos
  · exact firstControlDefectTensorCoefficient_22_2_pos
  · exact firstControlDefectTensorCoefficient_22_3_pos
  · exact firstControlDefectTensorCoefficient_22_4_pos
  · exact firstControlDefectTensorCoefficient_22_5_pos
  · exact firstControlDefectTensorCoefficient_22_6_pos
  · exact firstControlDefectTensorCoefficient_22_7_pos
  · exact firstControlDefectTensorCoefficient_22_8_pos
  · exact firstControlDefectTensorCoefficient_22_9_pos

theorem firstControlDefectTensorCoefficient_row23_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 23 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_23_0_pos
  · exact firstControlDefectTensorCoefficient_23_1_pos
  · exact firstControlDefectTensorCoefficient_23_2_pos
  · exact firstControlDefectTensorCoefficient_23_3_pos
  · exact firstControlDefectTensorCoefficient_23_4_pos
  · exact firstControlDefectTensorCoefficient_23_5_pos
  · exact firstControlDefectTensorCoefficient_23_6_pos
  · exact firstControlDefectTensorCoefficient_23_7_pos
  · exact firstControlDefectTensorCoefficient_23_8_pos
  · exact firstControlDefectTensorCoefficient_23_9_pos

theorem firstControlDefectTensorCoefficient_row24_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 24 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_24_0_pos
  · exact firstControlDefectTensorCoefficient_24_1_pos
  · exact firstControlDefectTensorCoefficient_24_2_pos
  · exact firstControlDefectTensorCoefficient_24_3_pos
  · exact firstControlDefectTensorCoefficient_24_4_pos
  · exact firstControlDefectTensorCoefficient_24_5_pos
  · exact firstControlDefectTensorCoefficient_24_6_pos
  · exact firstControlDefectTensorCoefficient_24_7_pos
  · exact firstControlDefectTensorCoefficient_24_8_pos
  · exact firstControlDefectTensorCoefficient_24_9_pos

theorem firstControlDefectTensorCoefficient_row25_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 25 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_25_0_pos
  · exact firstControlDefectTensorCoefficient_25_1_pos
  · exact firstControlDefectTensorCoefficient_25_2_pos
  · exact firstControlDefectTensorCoefficient_25_3_pos
  · exact firstControlDefectTensorCoefficient_25_4_pos
  · exact firstControlDefectTensorCoefficient_25_5_pos
  · exact firstControlDefectTensorCoefficient_25_6_pos
  · exact firstControlDefectTensorCoefficient_25_7_pos
  · exact firstControlDefectTensorCoefficient_25_8_pos
  · exact firstControlDefectTensorCoefficient_25_9_pos

theorem firstControlDefectTensorCoefficient_row26_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 26 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_26_0_pos
  · exact firstControlDefectTensorCoefficient_26_1_pos
  · exact firstControlDefectTensorCoefficient_26_2_pos
  · exact firstControlDefectTensorCoefficient_26_3_pos
  · exact firstControlDefectTensorCoefficient_26_4_pos
  · exact firstControlDefectTensorCoefficient_26_5_pos
  · exact firstControlDefectTensorCoefficient_26_6_pos
  · exact firstControlDefectTensorCoefficient_26_7_pos
  · exact firstControlDefectTensorCoefficient_26_8_pos
  · exact firstControlDefectTensorCoefficient_26_9_pos

theorem firstControlDefectTensorCoefficient_row27_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 27 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_27_0_pos
  · exact firstControlDefectTensorCoefficient_27_1_pos
  · exact firstControlDefectTensorCoefficient_27_2_pos
  · exact firstControlDefectTensorCoefficient_27_3_pos
  · exact firstControlDefectTensorCoefficient_27_4_pos
  · exact firstControlDefectTensorCoefficient_27_5_pos
  · exact firstControlDefectTensorCoefficient_27_6_pos
  · exact firstControlDefectTensorCoefficient_27_7_pos
  · exact firstControlDefectTensorCoefficient_27_8_pos
  · exact firstControlDefectTensorCoefficient_27_9_pos

theorem firstControlDefectTensorCoefficient_row28_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 28 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_28_0_pos
  · exact firstControlDefectTensorCoefficient_28_1_pos
  · exact firstControlDefectTensorCoefficient_28_2_pos
  · exact firstControlDefectTensorCoefficient_28_3_pos
  · exact firstControlDefectTensorCoefficient_28_4_pos
  · exact firstControlDefectTensorCoefficient_28_5_pos
  · exact firstControlDefectTensorCoefficient_28_6_pos
  · exact firstControlDefectTensorCoefficient_28_7_pos
  · exact firstControlDefectTensorCoefficient_28_8_pos
  · exact firstControlDefectTensorCoefficient_28_9_pos

theorem firstControlDefectTensorCoefficient_row29_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 29 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_29_0_pos
  · exact firstControlDefectTensorCoefficient_29_1_pos
  · exact firstControlDefectTensorCoefficient_29_2_pos
  · exact firstControlDefectTensorCoefficient_29_3_pos
  · exact firstControlDefectTensorCoefficient_29_4_pos
  · exact firstControlDefectTensorCoefficient_29_5_pos
  · exact firstControlDefectTensorCoefficient_29_6_pos
  · exact firstControlDefectTensorCoefficient_29_7_pos
  · exact firstControlDefectTensorCoefficient_29_8_pos
  · exact firstControlDefectTensorCoefficient_29_9_pos

theorem firstControlDefectTensorCoefficient_row30_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 30 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_30_0_pos
  · exact firstControlDefectTensorCoefficient_30_1_pos
  · exact firstControlDefectTensorCoefficient_30_2_pos
  · exact firstControlDefectTensorCoefficient_30_3_pos
  · exact firstControlDefectTensorCoefficient_30_4_pos
  · exact firstControlDefectTensorCoefficient_30_5_pos
  · exact firstControlDefectTensorCoefficient_30_6_pos
  · exact firstControlDefectTensorCoefficient_30_7_pos
  · exact firstControlDefectTensorCoefficient_30_8_pos
  · exact firstControlDefectTensorCoefficient_30_9_pos

theorem firstControlDefectTensorCoefficient_row31_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 31 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_31_0_pos
  · exact firstControlDefectTensorCoefficient_31_1_pos
  · exact firstControlDefectTensorCoefficient_31_2_pos
  · exact firstControlDefectTensorCoefficient_31_3_pos
  · exact firstControlDefectTensorCoefficient_31_4_pos
  · exact firstControlDefectTensorCoefficient_31_5_pos
  · exact firstControlDefectTensorCoefficient_31_6_pos
  · exact firstControlDefectTensorCoefficient_31_7_pos
  · exact firstControlDefectTensorCoefficient_31_8_pos
  · exact firstControlDefectTensorCoefficient_31_9_pos

theorem firstControlDefectTensorCoefficient_row32_pos (B : Fin 10) :
    0<firstControlDefectTensorCoefficient 32 B := by
  fin_cases B
  · exact firstControlDefectTensorCoefficient_32_0_pos
  · exact firstControlDefectTensorCoefficient_32_1_pos
  · exact firstControlDefectTensorCoefficient_32_2_pos
  · exact firstControlDefectTensorCoefficient_32_3_pos
  · exact firstControlDefectTensorCoefficient_32_4_pos
  · exact firstControlDefectTensorCoefficient_32_5_pos
  · exact firstControlDefectTensorCoefficient_32_6_pos
  · exact firstControlDefectTensorCoefficient_32_7_pos
  · exact firstControlDefectTensorCoefficient_32_8_pos
  · exact firstControlDefectTensorCoefficient_32_9_pos

theorem firstControlDefectTensorCoefficient_pos (A : Fin 33) (B : Fin 10) :
    0<firstControlDefectTensorCoefficient A B := by
  fin_cases A
  · exact firstControlDefectTensorCoefficient_row0_pos B
  · exact firstControlDefectTensorCoefficient_row1_pos B
  · exact firstControlDefectTensorCoefficient_row2_pos B
  · exact firstControlDefectTensorCoefficient_row3_pos B
  · exact firstControlDefectTensorCoefficient_row4_pos B
  · exact firstControlDefectTensorCoefficient_row5_pos B
  · exact firstControlDefectTensorCoefficient_row6_pos B
  · exact firstControlDefectTensorCoefficient_row7_pos B
  · exact firstControlDefectTensorCoefficient_row8_pos B
  · exact firstControlDefectTensorCoefficient_row9_pos B
  · exact firstControlDefectTensorCoefficient_row10_pos B
  · exact firstControlDefectTensorCoefficient_row11_pos B
  · exact firstControlDefectTensorCoefficient_row12_pos B
  · exact firstControlDefectTensorCoefficient_row13_pos B
  · exact firstControlDefectTensorCoefficient_row14_pos B
  · exact firstControlDefectTensorCoefficient_row15_pos B
  · exact firstControlDefectTensorCoefficient_row16_pos B
  · exact firstControlDefectTensorCoefficient_row17_pos B
  · exact firstControlDefectTensorCoefficient_row18_pos B
  · exact firstControlDefectTensorCoefficient_row19_pos B
  · exact firstControlDefectTensorCoefficient_row20_pos B
  · exact firstControlDefectTensorCoefficient_row21_pos B
  · exact firstControlDefectTensorCoefficient_row22_pos B
  · exact firstControlDefectTensorCoefficient_row23_pos B
  · exact firstControlDefectTensorCoefficient_row24_pos B
  · exact firstControlDefectTensorCoefficient_row25_pos B
  · exact firstControlDefectTensorCoefficient_row26_pos B
  · exact firstControlDefectTensorCoefficient_row27_pos B
  · exact firstControlDefectTensorCoefficient_row28_pos B
  · exact firstControlDefectTensorCoefficient_row29_pos B
  · exact firstControlDefectTensorCoefficient_row30_pos B
  · exact firstControlDefectTensorCoefficient_row31_pos B
  · exact firstControlDefectTensorCoefficient_row32_pos B

theorem kineticBernstein_pos (n : ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hf : ∀ i<n+1,0<f i) (ht0 : 0≤t) (ht1 : t≤1) :
    0<kineticBernstein n f t := by
  unfold kineticBernstein
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hf i (Finset.mem_range.mp hi)).le
      (mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (sub_nonneg.mpr ht1) _))
  · by_cases ht : t=1
    · refine ⟨n,Finset.mem_range.mpr (by omega),?_⟩
      simpa [ht,unscaledBernstein] using hf n (by omega)
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      have htp : 0<1-t := by
        have hlt : t<1 := lt_of_le_of_ne ht1 ht
        linarith
      simpa [unscaledBernstein] using mul_pos (hf 0 (by omega)) (pow_pos htp n)

theorem firstControlDefectQuotient_unit_pos (t v : ℝ)
    (ht0 : 0≤t) (ht1 : t≤1) (hv0 : 0≤v) (hv1 : v≤1) :
    0<firstControlDefectQuotient ((4/5)*t) ((361/25)*v) := by
  rw [←firstControlDefectTensorValue_reconstruction]
  apply kineticBernstein_pos 32 _ t _ ht0 ht1
  intro A hA
  apply kineticBernstein_pos 9 _ v _ hv0 hv1
  intro B hB
  exact firstControlDefectTensorCoefficient_pos ⟨A,hA⟩ ⟨B,hB⟩

theorem firstControlDefectQuotient_pos (h r : ℝ)
    (hh0 : 0≤h) (hh1 : h≤4/5) (hr0 : 0≤r) (hr1 : r≤361/25) :
    0<firstControlDefectQuotient h r := by
  have ht0 : 0≤h/(4/5:ℝ) := div_nonneg hh0 (by norm_num)
  have ht1 : h/(4/5:ℝ)≤1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hh1)
  have hv0 : 0≤r/(361/25:ℝ) := div_nonneg hr0 (by norm_num)
  have hv1 : r/(361/25:ℝ)≤1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hr1)
  have hp := firstControlDefectQuotient_unit_pos (h/(4/5)) (r/(361/25)) ht0 ht1 hv0 hv1
  have he : (4/5:ℝ)*(h/(4/5))=h := by ring
  have re : (361/25:ℝ)*(r/(361/25))=r := by ring
  simpa only [he,re] using hp

theorem reducedKineticControl_zero_pos (h r Z : ℝ)
    (hh0 : 0<h) (hh1 : h≤4/5) (hr0 : 0≤r) (hr1 : r≤361/25) :
    0<reducedKineticControl h (9-r*h^2) Z 0 := by
  rw [reducedKineticControl_zero,firstControl_defect_factor]
  exact mul_pos (pow_pos hh0 _) (firstControlDefectQuotient_pos h r hh0.le hh1 hr0 hr1)

end
end HTGeometry.ThetaRatioKineticContraction
