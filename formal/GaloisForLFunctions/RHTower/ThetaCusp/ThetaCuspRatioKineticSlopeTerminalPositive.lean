import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalReconstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow0
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow7
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow9
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow11
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow12
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow13
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow14
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow15
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow16
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow17
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow18
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow19
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow20
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow21
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow22
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow23
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow24
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow25
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow26
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow27
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow28
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow29
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow30
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow31
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow32
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow33
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow34
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow35
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow36
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow37
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalTensorRow38
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeTerminalTensorCoefficient_row0_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 0 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_0_0_pos
  · exact slopeTerminalTensorCoefficient_0_1_pos
  · exact slopeTerminalTensorCoefficient_0_2_pos
  · exact slopeTerminalTensorCoefficient_0_3_pos
  · exact slopeTerminalTensorCoefficient_0_4_pos
  · exact slopeTerminalTensorCoefficient_0_5_pos
  · exact slopeTerminalTensorCoefficient_0_6_pos
  · exact slopeTerminalTensorCoefficient_0_7_pos
  · exact slopeTerminalTensorCoefficient_0_8_pos
  · exact slopeTerminalTensorCoefficient_0_9_pos

theorem slopeTerminalTensorCoefficient_row1_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 1 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_1_0_pos
  · exact slopeTerminalTensorCoefficient_1_1_pos
  · exact slopeTerminalTensorCoefficient_1_2_pos
  · exact slopeTerminalTensorCoefficient_1_3_pos
  · exact slopeTerminalTensorCoefficient_1_4_pos
  · exact slopeTerminalTensorCoefficient_1_5_pos
  · exact slopeTerminalTensorCoefficient_1_6_pos
  · exact slopeTerminalTensorCoefficient_1_7_pos
  · exact slopeTerminalTensorCoefficient_1_8_pos
  · exact slopeTerminalTensorCoefficient_1_9_pos

theorem slopeTerminalTensorCoefficient_row2_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 2 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_2_0_pos
  · exact slopeTerminalTensorCoefficient_2_1_pos
  · exact slopeTerminalTensorCoefficient_2_2_pos
  · exact slopeTerminalTensorCoefficient_2_3_pos
  · exact slopeTerminalTensorCoefficient_2_4_pos
  · exact slopeTerminalTensorCoefficient_2_5_pos
  · exact slopeTerminalTensorCoefficient_2_6_pos
  · exact slopeTerminalTensorCoefficient_2_7_pos
  · exact slopeTerminalTensorCoefficient_2_8_pos
  · exact slopeTerminalTensorCoefficient_2_9_pos

theorem slopeTerminalTensorCoefficient_row3_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 3 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_3_0_pos
  · exact slopeTerminalTensorCoefficient_3_1_pos
  · exact slopeTerminalTensorCoefficient_3_2_pos
  · exact slopeTerminalTensorCoefficient_3_3_pos
  · exact slopeTerminalTensorCoefficient_3_4_pos
  · exact slopeTerminalTensorCoefficient_3_5_pos
  · exact slopeTerminalTensorCoefficient_3_6_pos
  · exact slopeTerminalTensorCoefficient_3_7_pos
  · exact slopeTerminalTensorCoefficient_3_8_pos
  · exact slopeTerminalTensorCoefficient_3_9_pos

theorem slopeTerminalTensorCoefficient_row4_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 4 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_4_0_pos
  · exact slopeTerminalTensorCoefficient_4_1_pos
  · exact slopeTerminalTensorCoefficient_4_2_pos
  · exact slopeTerminalTensorCoefficient_4_3_pos
  · exact slopeTerminalTensorCoefficient_4_4_pos
  · exact slopeTerminalTensorCoefficient_4_5_pos
  · exact slopeTerminalTensorCoefficient_4_6_pos
  · exact slopeTerminalTensorCoefficient_4_7_pos
  · exact slopeTerminalTensorCoefficient_4_8_pos
  · exact slopeTerminalTensorCoefficient_4_9_pos

theorem slopeTerminalTensorCoefficient_row5_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 5 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_5_0_pos
  · exact slopeTerminalTensorCoefficient_5_1_pos
  · exact slopeTerminalTensorCoefficient_5_2_pos
  · exact slopeTerminalTensorCoefficient_5_3_pos
  · exact slopeTerminalTensorCoefficient_5_4_pos
  · exact slopeTerminalTensorCoefficient_5_5_pos
  · exact slopeTerminalTensorCoefficient_5_6_pos
  · exact slopeTerminalTensorCoefficient_5_7_pos
  · exact slopeTerminalTensorCoefficient_5_8_pos
  · exact slopeTerminalTensorCoefficient_5_9_pos

theorem slopeTerminalTensorCoefficient_row6_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 6 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_6_0_pos
  · exact slopeTerminalTensorCoefficient_6_1_pos
  · exact slopeTerminalTensorCoefficient_6_2_pos
  · exact slopeTerminalTensorCoefficient_6_3_pos
  · exact slopeTerminalTensorCoefficient_6_4_pos
  · exact slopeTerminalTensorCoefficient_6_5_pos
  · exact slopeTerminalTensorCoefficient_6_6_pos
  · exact slopeTerminalTensorCoefficient_6_7_pos
  · exact slopeTerminalTensorCoefficient_6_8_pos
  · exact slopeTerminalTensorCoefficient_6_9_pos

theorem slopeTerminalTensorCoefficient_row7_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 7 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_7_0_pos
  · exact slopeTerminalTensorCoefficient_7_1_pos
  · exact slopeTerminalTensorCoefficient_7_2_pos
  · exact slopeTerminalTensorCoefficient_7_3_pos
  · exact slopeTerminalTensorCoefficient_7_4_pos
  · exact slopeTerminalTensorCoefficient_7_5_pos
  · exact slopeTerminalTensorCoefficient_7_6_pos
  · exact slopeTerminalTensorCoefficient_7_7_pos
  · exact slopeTerminalTensorCoefficient_7_8_pos
  · exact slopeTerminalTensorCoefficient_7_9_pos

theorem slopeTerminalTensorCoefficient_row8_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 8 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_8_0_pos
  · exact slopeTerminalTensorCoefficient_8_1_pos
  · exact slopeTerminalTensorCoefficient_8_2_pos
  · exact slopeTerminalTensorCoefficient_8_3_pos
  · exact slopeTerminalTensorCoefficient_8_4_pos
  · exact slopeTerminalTensorCoefficient_8_5_pos
  · exact slopeTerminalTensorCoefficient_8_6_pos
  · exact slopeTerminalTensorCoefficient_8_7_pos
  · exact slopeTerminalTensorCoefficient_8_8_pos
  · exact slopeTerminalTensorCoefficient_8_9_pos

theorem slopeTerminalTensorCoefficient_row9_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 9 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_9_0_pos
  · exact slopeTerminalTensorCoefficient_9_1_pos
  · exact slopeTerminalTensorCoefficient_9_2_pos
  · exact slopeTerminalTensorCoefficient_9_3_pos
  · exact slopeTerminalTensorCoefficient_9_4_pos
  · exact slopeTerminalTensorCoefficient_9_5_pos
  · exact slopeTerminalTensorCoefficient_9_6_pos
  · exact slopeTerminalTensorCoefficient_9_7_pos
  · exact slopeTerminalTensorCoefficient_9_8_pos
  · exact slopeTerminalTensorCoefficient_9_9_pos

theorem slopeTerminalTensorCoefficient_row10_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 10 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_10_0_pos
  · exact slopeTerminalTensorCoefficient_10_1_pos
  · exact slopeTerminalTensorCoefficient_10_2_pos
  · exact slopeTerminalTensorCoefficient_10_3_pos
  · exact slopeTerminalTensorCoefficient_10_4_pos
  · exact slopeTerminalTensorCoefficient_10_5_pos
  · exact slopeTerminalTensorCoefficient_10_6_pos
  · exact slopeTerminalTensorCoefficient_10_7_pos
  · exact slopeTerminalTensorCoefficient_10_8_pos
  · exact slopeTerminalTensorCoefficient_10_9_pos

theorem slopeTerminalTensorCoefficient_row11_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 11 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_11_0_pos
  · exact slopeTerminalTensorCoefficient_11_1_pos
  · exact slopeTerminalTensorCoefficient_11_2_pos
  · exact slopeTerminalTensorCoefficient_11_3_pos
  · exact slopeTerminalTensorCoefficient_11_4_pos
  · exact slopeTerminalTensorCoefficient_11_5_pos
  · exact slopeTerminalTensorCoefficient_11_6_pos
  · exact slopeTerminalTensorCoefficient_11_7_pos
  · exact slopeTerminalTensorCoefficient_11_8_pos
  · exact slopeTerminalTensorCoefficient_11_9_pos

theorem slopeTerminalTensorCoefficient_row12_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 12 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_12_0_pos
  · exact slopeTerminalTensorCoefficient_12_1_pos
  · exact slopeTerminalTensorCoefficient_12_2_pos
  · exact slopeTerminalTensorCoefficient_12_3_pos
  · exact slopeTerminalTensorCoefficient_12_4_pos
  · exact slopeTerminalTensorCoefficient_12_5_pos
  · exact slopeTerminalTensorCoefficient_12_6_pos
  · exact slopeTerminalTensorCoefficient_12_7_pos
  · exact slopeTerminalTensorCoefficient_12_8_pos
  · exact slopeTerminalTensorCoefficient_12_9_pos

theorem slopeTerminalTensorCoefficient_row13_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 13 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_13_0_pos
  · exact slopeTerminalTensorCoefficient_13_1_pos
  · exact slopeTerminalTensorCoefficient_13_2_pos
  · exact slopeTerminalTensorCoefficient_13_3_pos
  · exact slopeTerminalTensorCoefficient_13_4_pos
  · exact slopeTerminalTensorCoefficient_13_5_pos
  · exact slopeTerminalTensorCoefficient_13_6_pos
  · exact slopeTerminalTensorCoefficient_13_7_pos
  · exact slopeTerminalTensorCoefficient_13_8_pos
  · exact slopeTerminalTensorCoefficient_13_9_pos

theorem slopeTerminalTensorCoefficient_row14_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 14 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_14_0_pos
  · exact slopeTerminalTensorCoefficient_14_1_pos
  · exact slopeTerminalTensorCoefficient_14_2_pos
  · exact slopeTerminalTensorCoefficient_14_3_pos
  · exact slopeTerminalTensorCoefficient_14_4_pos
  · exact slopeTerminalTensorCoefficient_14_5_pos
  · exact slopeTerminalTensorCoefficient_14_6_pos
  · exact slopeTerminalTensorCoefficient_14_7_pos
  · exact slopeTerminalTensorCoefficient_14_8_pos
  · exact slopeTerminalTensorCoefficient_14_9_pos

theorem slopeTerminalTensorCoefficient_row15_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 15 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_15_0_pos
  · exact slopeTerminalTensorCoefficient_15_1_pos
  · exact slopeTerminalTensorCoefficient_15_2_pos
  · exact slopeTerminalTensorCoefficient_15_3_pos
  · exact slopeTerminalTensorCoefficient_15_4_pos
  · exact slopeTerminalTensorCoefficient_15_5_pos
  · exact slopeTerminalTensorCoefficient_15_6_pos
  · exact slopeTerminalTensorCoefficient_15_7_pos
  · exact slopeTerminalTensorCoefficient_15_8_pos
  · exact slopeTerminalTensorCoefficient_15_9_pos

theorem slopeTerminalTensorCoefficient_row16_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 16 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_16_0_pos
  · exact slopeTerminalTensorCoefficient_16_1_pos
  · exact slopeTerminalTensorCoefficient_16_2_pos
  · exact slopeTerminalTensorCoefficient_16_3_pos
  · exact slopeTerminalTensorCoefficient_16_4_pos
  · exact slopeTerminalTensorCoefficient_16_5_pos
  · exact slopeTerminalTensorCoefficient_16_6_pos
  · exact slopeTerminalTensorCoefficient_16_7_pos
  · exact slopeTerminalTensorCoefficient_16_8_pos
  · exact slopeTerminalTensorCoefficient_16_9_pos

theorem slopeTerminalTensorCoefficient_row17_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 17 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_17_0_pos
  · exact slopeTerminalTensorCoefficient_17_1_pos
  · exact slopeTerminalTensorCoefficient_17_2_pos
  · exact slopeTerminalTensorCoefficient_17_3_pos
  · exact slopeTerminalTensorCoefficient_17_4_pos
  · exact slopeTerminalTensorCoefficient_17_5_pos
  · exact slopeTerminalTensorCoefficient_17_6_pos
  · exact slopeTerminalTensorCoefficient_17_7_pos
  · exact slopeTerminalTensorCoefficient_17_8_pos
  · exact slopeTerminalTensorCoefficient_17_9_pos

theorem slopeTerminalTensorCoefficient_row18_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 18 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_18_0_pos
  · exact slopeTerminalTensorCoefficient_18_1_pos
  · exact slopeTerminalTensorCoefficient_18_2_pos
  · exact slopeTerminalTensorCoefficient_18_3_pos
  · exact slopeTerminalTensorCoefficient_18_4_pos
  · exact slopeTerminalTensorCoefficient_18_5_pos
  · exact slopeTerminalTensorCoefficient_18_6_pos
  · exact slopeTerminalTensorCoefficient_18_7_pos
  · exact slopeTerminalTensorCoefficient_18_8_pos
  · exact slopeTerminalTensorCoefficient_18_9_pos

theorem slopeTerminalTensorCoefficient_row19_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 19 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_19_0_pos
  · exact slopeTerminalTensorCoefficient_19_1_pos
  · exact slopeTerminalTensorCoefficient_19_2_pos
  · exact slopeTerminalTensorCoefficient_19_3_pos
  · exact slopeTerminalTensorCoefficient_19_4_pos
  · exact slopeTerminalTensorCoefficient_19_5_pos
  · exact slopeTerminalTensorCoefficient_19_6_pos
  · exact slopeTerminalTensorCoefficient_19_7_pos
  · exact slopeTerminalTensorCoefficient_19_8_pos
  · exact slopeTerminalTensorCoefficient_19_9_pos

theorem slopeTerminalTensorCoefficient_row20_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 20 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_20_0_pos
  · exact slopeTerminalTensorCoefficient_20_1_pos
  · exact slopeTerminalTensorCoefficient_20_2_pos
  · exact slopeTerminalTensorCoefficient_20_3_pos
  · exact slopeTerminalTensorCoefficient_20_4_pos
  · exact slopeTerminalTensorCoefficient_20_5_pos
  · exact slopeTerminalTensorCoefficient_20_6_pos
  · exact slopeTerminalTensorCoefficient_20_7_pos
  · exact slopeTerminalTensorCoefficient_20_8_pos
  · exact slopeTerminalTensorCoefficient_20_9_pos

theorem slopeTerminalTensorCoefficient_row21_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 21 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_21_0_pos
  · exact slopeTerminalTensorCoefficient_21_1_pos
  · exact slopeTerminalTensorCoefficient_21_2_pos
  · exact slopeTerminalTensorCoefficient_21_3_pos
  · exact slopeTerminalTensorCoefficient_21_4_pos
  · exact slopeTerminalTensorCoefficient_21_5_pos
  · exact slopeTerminalTensorCoefficient_21_6_pos
  · exact slopeTerminalTensorCoefficient_21_7_pos
  · exact slopeTerminalTensorCoefficient_21_8_pos
  · exact slopeTerminalTensorCoefficient_21_9_pos

theorem slopeTerminalTensorCoefficient_row22_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 22 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_22_0_pos
  · exact slopeTerminalTensorCoefficient_22_1_pos
  · exact slopeTerminalTensorCoefficient_22_2_pos
  · exact slopeTerminalTensorCoefficient_22_3_pos
  · exact slopeTerminalTensorCoefficient_22_4_pos
  · exact slopeTerminalTensorCoefficient_22_5_pos
  · exact slopeTerminalTensorCoefficient_22_6_pos
  · exact slopeTerminalTensorCoefficient_22_7_pos
  · exact slopeTerminalTensorCoefficient_22_8_pos
  · exact slopeTerminalTensorCoefficient_22_9_pos

theorem slopeTerminalTensorCoefficient_row23_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 23 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_23_0_pos
  · exact slopeTerminalTensorCoefficient_23_1_pos
  · exact slopeTerminalTensorCoefficient_23_2_pos
  · exact slopeTerminalTensorCoefficient_23_3_pos
  · exact slopeTerminalTensorCoefficient_23_4_pos
  · exact slopeTerminalTensorCoefficient_23_5_pos
  · exact slopeTerminalTensorCoefficient_23_6_pos
  · exact slopeTerminalTensorCoefficient_23_7_pos
  · exact slopeTerminalTensorCoefficient_23_8_pos
  · exact slopeTerminalTensorCoefficient_23_9_pos

theorem slopeTerminalTensorCoefficient_row24_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 24 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_24_0_pos
  · exact slopeTerminalTensorCoefficient_24_1_pos
  · exact slopeTerminalTensorCoefficient_24_2_pos
  · exact slopeTerminalTensorCoefficient_24_3_pos
  · exact slopeTerminalTensorCoefficient_24_4_pos
  · exact slopeTerminalTensorCoefficient_24_5_pos
  · exact slopeTerminalTensorCoefficient_24_6_pos
  · exact slopeTerminalTensorCoefficient_24_7_pos
  · exact slopeTerminalTensorCoefficient_24_8_pos
  · exact slopeTerminalTensorCoefficient_24_9_pos

theorem slopeTerminalTensorCoefficient_row25_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 25 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_25_0_pos
  · exact slopeTerminalTensorCoefficient_25_1_pos
  · exact slopeTerminalTensorCoefficient_25_2_pos
  · exact slopeTerminalTensorCoefficient_25_3_pos
  · exact slopeTerminalTensorCoefficient_25_4_pos
  · exact slopeTerminalTensorCoefficient_25_5_pos
  · exact slopeTerminalTensorCoefficient_25_6_pos
  · exact slopeTerminalTensorCoefficient_25_7_pos
  · exact slopeTerminalTensorCoefficient_25_8_pos
  · exact slopeTerminalTensorCoefficient_25_9_pos

theorem slopeTerminalTensorCoefficient_row26_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 26 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_26_0_pos
  · exact slopeTerminalTensorCoefficient_26_1_pos
  · exact slopeTerminalTensorCoefficient_26_2_pos
  · exact slopeTerminalTensorCoefficient_26_3_pos
  · exact slopeTerminalTensorCoefficient_26_4_pos
  · exact slopeTerminalTensorCoefficient_26_5_pos
  · exact slopeTerminalTensorCoefficient_26_6_pos
  · exact slopeTerminalTensorCoefficient_26_7_pos
  · exact slopeTerminalTensorCoefficient_26_8_pos
  · exact slopeTerminalTensorCoefficient_26_9_pos

theorem slopeTerminalTensorCoefficient_row27_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 27 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_27_0_pos
  · exact slopeTerminalTensorCoefficient_27_1_pos
  · exact slopeTerminalTensorCoefficient_27_2_pos
  · exact slopeTerminalTensorCoefficient_27_3_pos
  · exact slopeTerminalTensorCoefficient_27_4_pos
  · exact slopeTerminalTensorCoefficient_27_5_pos
  · exact slopeTerminalTensorCoefficient_27_6_pos
  · exact slopeTerminalTensorCoefficient_27_7_pos
  · exact slopeTerminalTensorCoefficient_27_8_pos
  · exact slopeTerminalTensorCoefficient_27_9_pos

theorem slopeTerminalTensorCoefficient_row28_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 28 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_28_0_pos
  · exact slopeTerminalTensorCoefficient_28_1_pos
  · exact slopeTerminalTensorCoefficient_28_2_pos
  · exact slopeTerminalTensorCoefficient_28_3_pos
  · exact slopeTerminalTensorCoefficient_28_4_pos
  · exact slopeTerminalTensorCoefficient_28_5_pos
  · exact slopeTerminalTensorCoefficient_28_6_pos
  · exact slopeTerminalTensorCoefficient_28_7_pos
  · exact slopeTerminalTensorCoefficient_28_8_pos
  · exact slopeTerminalTensorCoefficient_28_9_pos

theorem slopeTerminalTensorCoefficient_row29_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 29 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_29_0_pos
  · exact slopeTerminalTensorCoefficient_29_1_pos
  · exact slopeTerminalTensorCoefficient_29_2_pos
  · exact slopeTerminalTensorCoefficient_29_3_pos
  · exact slopeTerminalTensorCoefficient_29_4_pos
  · exact slopeTerminalTensorCoefficient_29_5_pos
  · exact slopeTerminalTensorCoefficient_29_6_pos
  · exact slopeTerminalTensorCoefficient_29_7_pos
  · exact slopeTerminalTensorCoefficient_29_8_pos
  · exact slopeTerminalTensorCoefficient_29_9_pos

theorem slopeTerminalTensorCoefficient_row30_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 30 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_30_0_pos
  · exact slopeTerminalTensorCoefficient_30_1_pos
  · exact slopeTerminalTensorCoefficient_30_2_pos
  · exact slopeTerminalTensorCoefficient_30_3_pos
  · exact slopeTerminalTensorCoefficient_30_4_pos
  · exact slopeTerminalTensorCoefficient_30_5_pos
  · exact slopeTerminalTensorCoefficient_30_6_pos
  · exact slopeTerminalTensorCoefficient_30_7_pos
  · exact slopeTerminalTensorCoefficient_30_8_pos
  · exact slopeTerminalTensorCoefficient_30_9_pos

theorem slopeTerminalTensorCoefficient_row31_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 31 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_31_0_pos
  · exact slopeTerminalTensorCoefficient_31_1_pos
  · exact slopeTerminalTensorCoefficient_31_2_pos
  · exact slopeTerminalTensorCoefficient_31_3_pos
  · exact slopeTerminalTensorCoefficient_31_4_pos
  · exact slopeTerminalTensorCoefficient_31_5_pos
  · exact slopeTerminalTensorCoefficient_31_6_pos
  · exact slopeTerminalTensorCoefficient_31_7_pos
  · exact slopeTerminalTensorCoefficient_31_8_pos
  · exact slopeTerminalTensorCoefficient_31_9_pos

theorem slopeTerminalTensorCoefficient_row32_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 32 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_32_0_pos
  · exact slopeTerminalTensorCoefficient_32_1_pos
  · exact slopeTerminalTensorCoefficient_32_2_pos
  · exact slopeTerminalTensorCoefficient_32_3_pos
  · exact slopeTerminalTensorCoefficient_32_4_pos
  · exact slopeTerminalTensorCoefficient_32_5_pos
  · exact slopeTerminalTensorCoefficient_32_6_pos
  · exact slopeTerminalTensorCoefficient_32_7_pos
  · exact slopeTerminalTensorCoefficient_32_8_pos
  · exact slopeTerminalTensorCoefficient_32_9_pos

theorem slopeTerminalTensorCoefficient_row33_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 33 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_33_0_pos
  · exact slopeTerminalTensorCoefficient_33_1_pos
  · exact slopeTerminalTensorCoefficient_33_2_pos
  · exact slopeTerminalTensorCoefficient_33_3_pos
  · exact slopeTerminalTensorCoefficient_33_4_pos
  · exact slopeTerminalTensorCoefficient_33_5_pos
  · exact slopeTerminalTensorCoefficient_33_6_pos
  · exact slopeTerminalTensorCoefficient_33_7_pos
  · exact slopeTerminalTensorCoefficient_33_8_pos
  · exact slopeTerminalTensorCoefficient_33_9_pos

theorem slopeTerminalTensorCoefficient_row34_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 34 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_34_0_pos
  · exact slopeTerminalTensorCoefficient_34_1_pos
  · exact slopeTerminalTensorCoefficient_34_2_pos
  · exact slopeTerminalTensorCoefficient_34_3_pos
  · exact slopeTerminalTensorCoefficient_34_4_pos
  · exact slopeTerminalTensorCoefficient_34_5_pos
  · exact slopeTerminalTensorCoefficient_34_6_pos
  · exact slopeTerminalTensorCoefficient_34_7_pos
  · exact slopeTerminalTensorCoefficient_34_8_pos
  · exact slopeTerminalTensorCoefficient_34_9_pos

theorem slopeTerminalTensorCoefficient_row35_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 35 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_35_0_pos
  · exact slopeTerminalTensorCoefficient_35_1_pos
  · exact slopeTerminalTensorCoefficient_35_2_pos
  · exact slopeTerminalTensorCoefficient_35_3_pos
  · exact slopeTerminalTensorCoefficient_35_4_pos
  · exact slopeTerminalTensorCoefficient_35_5_pos
  · exact slopeTerminalTensorCoefficient_35_6_pos
  · exact slopeTerminalTensorCoefficient_35_7_pos
  · exact slopeTerminalTensorCoefficient_35_8_pos
  · exact slopeTerminalTensorCoefficient_35_9_pos

theorem slopeTerminalTensorCoefficient_row36_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 36 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_36_0_pos
  · exact slopeTerminalTensorCoefficient_36_1_pos
  · exact slopeTerminalTensorCoefficient_36_2_pos
  · exact slopeTerminalTensorCoefficient_36_3_pos
  · exact slopeTerminalTensorCoefficient_36_4_pos
  · exact slopeTerminalTensorCoefficient_36_5_pos
  · exact slopeTerminalTensorCoefficient_36_6_pos
  · exact slopeTerminalTensorCoefficient_36_7_pos
  · exact slopeTerminalTensorCoefficient_36_8_pos
  · exact slopeTerminalTensorCoefficient_36_9_pos

theorem slopeTerminalTensorCoefficient_row37_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 37 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_37_0_pos
  · exact slopeTerminalTensorCoefficient_37_1_pos
  · exact slopeTerminalTensorCoefficient_37_2_pos
  · exact slopeTerminalTensorCoefficient_37_3_pos
  · exact slopeTerminalTensorCoefficient_37_4_pos
  · exact slopeTerminalTensorCoefficient_37_5_pos
  · exact slopeTerminalTensorCoefficient_37_6_pos
  · exact slopeTerminalTensorCoefficient_37_7_pos
  · exact slopeTerminalTensorCoefficient_37_8_pos
  · exact slopeTerminalTensorCoefficient_37_9_pos

theorem slopeTerminalTensorCoefficient_row38_pos (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient 38 B := by
  fin_cases B
  · exact slopeTerminalTensorCoefficient_38_0_pos
  · exact slopeTerminalTensorCoefficient_38_1_pos
  · exact slopeTerminalTensorCoefficient_38_2_pos
  · exact slopeTerminalTensorCoefficient_38_3_pos
  · exact slopeTerminalTensorCoefficient_38_4_pos
  · exact slopeTerminalTensorCoefficient_38_5_pos
  · exact slopeTerminalTensorCoefficient_38_6_pos
  · exact slopeTerminalTensorCoefficient_38_7_pos
  · exact slopeTerminalTensorCoefficient_38_8_pos
  · exact slopeTerminalTensorCoefficient_38_9_pos

theorem slopeTerminalTensorCoefficient_pos (A : Fin 39) (B : Fin 10) :
    0 < slopeTerminalTensorCoefficient A B := by
  fin_cases A
  · exact slopeTerminalTensorCoefficient_row0_pos B
  · exact slopeTerminalTensorCoefficient_row1_pos B
  · exact slopeTerminalTensorCoefficient_row2_pos B
  · exact slopeTerminalTensorCoefficient_row3_pos B
  · exact slopeTerminalTensorCoefficient_row4_pos B
  · exact slopeTerminalTensorCoefficient_row5_pos B
  · exact slopeTerminalTensorCoefficient_row6_pos B
  · exact slopeTerminalTensorCoefficient_row7_pos B
  · exact slopeTerminalTensorCoefficient_row8_pos B
  · exact slopeTerminalTensorCoefficient_row9_pos B
  · exact slopeTerminalTensorCoefficient_row10_pos B
  · exact slopeTerminalTensorCoefficient_row11_pos B
  · exact slopeTerminalTensorCoefficient_row12_pos B
  · exact slopeTerminalTensorCoefficient_row13_pos B
  · exact slopeTerminalTensorCoefficient_row14_pos B
  · exact slopeTerminalTensorCoefficient_row15_pos B
  · exact slopeTerminalTensorCoefficient_row16_pos B
  · exact slopeTerminalTensorCoefficient_row17_pos B
  · exact slopeTerminalTensorCoefficient_row18_pos B
  · exact slopeTerminalTensorCoefficient_row19_pos B
  · exact slopeTerminalTensorCoefficient_row20_pos B
  · exact slopeTerminalTensorCoefficient_row21_pos B
  · exact slopeTerminalTensorCoefficient_row22_pos B
  · exact slopeTerminalTensorCoefficient_row23_pos B
  · exact slopeTerminalTensorCoefficient_row24_pos B
  · exact slopeTerminalTensorCoefficient_row25_pos B
  · exact slopeTerminalTensorCoefficient_row26_pos B
  · exact slopeTerminalTensorCoefficient_row27_pos B
  · exact slopeTerminalTensorCoefficient_row28_pos B
  · exact slopeTerminalTensorCoefficient_row29_pos B
  · exact slopeTerminalTensorCoefficient_row30_pos B
  · exact slopeTerminalTensorCoefficient_row31_pos B
  · exact slopeTerminalTensorCoefficient_row32_pos B
  · exact slopeTerminalTensorCoefficient_row33_pos B
  · exact slopeTerminalTensorCoefficient_row34_pos B
  · exact slopeTerminalTensorCoefficient_row35_pos B
  · exact slopeTerminalTensorCoefficient_row36_pos B
  · exact slopeTerminalTensorCoefficient_row37_pos B
  · exact slopeTerminalTensorCoefficient_row38_pos B

theorem slopeTerminalQuotient_unit_pos (t v : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < slopeTerminalQuotient ((4/5)*t) ((361/25)*v) := by
  rw [←slopeTerminalTensorValue_reconstruction]
  apply kineticBernstein_pos 38 _ t _ ht0 ht1
  intro A hA
  apply kineticBernstein_pos 9 _ v _ hv0 hv1
  intro B hB
  exact slopeTerminalTensorCoefficient_pos ⟨A,hA⟩ ⟨B,hB⟩

theorem slopeTerminalQuotient_pos (h r : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 4/5) (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    0 < slopeTerminalQuotient h r := by
  have ht0 : 0 ≤ h/(4/5:ℝ) := div_nonneg hh0 (by norm_num)
  have ht1 : h/(4/5:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hh1)
  have hv0 : 0 ≤ r/(361/25:ℝ) := div_nonneg hr0 (by norm_num)
  have hv1 : r/(361/25:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hr1)
  have hp := slopeTerminalQuotient_unit_pos (h/(4/5)) (r/(361/25)) ht0 ht1 hv0 hv1
  have he : (4/5:ℝ)*(h/(4/5))=h := by ring
  have re : (361/25:ℝ)*(r/(361/25))=r := by ring
  simpa only [he,re] using hp

theorem reducedKineticValue_terminal_deriv_neg (h r : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 4/5) (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    deriv (reducedKineticValue h (9-r*h^2)) (1/3) < 0 := by
  have hp := mul_pos (pow_pos hh0 4) (slopeTerminalQuotient_pos h r hh0.le hh1 hr0 hr1)
  rw [←slopeTerminal_factor,negKineticSlopeControl_terminal] at hp
  exact neg_pos.mp hp

end
end HTGeometry.ThetaRatioKineticContraction

