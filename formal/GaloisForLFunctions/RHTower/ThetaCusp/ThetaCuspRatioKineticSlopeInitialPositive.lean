import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialReconstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow0
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow7
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow9
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow11
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow12
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow13
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow14
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow15
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow16
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow17
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow18
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow19
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow20
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow21
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow22
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow23
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow24
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow25
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow26
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow27
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow28
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow29
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow30
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow31
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow32
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInitialTensorRow33
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInitialTensorCoefficient_row0_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 0 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_0_0_pos
  · exact slopeInitialTensorCoefficient_0_1_pos
  · exact slopeInitialTensorCoefficient_0_2_pos
  · exact slopeInitialTensorCoefficient_0_3_pos
  · exact slopeInitialTensorCoefficient_0_4_pos
  · exact slopeInitialTensorCoefficient_0_5_pos
  · exact slopeInitialTensorCoefficient_0_6_pos
  · exact slopeInitialTensorCoefficient_0_7_pos
  · exact slopeInitialTensorCoefficient_0_8_pos
  · exact slopeInitialTensorCoefficient_0_9_pos

theorem slopeInitialTensorCoefficient_row1_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 1 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_1_0_pos
  · exact slopeInitialTensorCoefficient_1_1_pos
  · exact slopeInitialTensorCoefficient_1_2_pos
  · exact slopeInitialTensorCoefficient_1_3_pos
  · exact slopeInitialTensorCoefficient_1_4_pos
  · exact slopeInitialTensorCoefficient_1_5_pos
  · exact slopeInitialTensorCoefficient_1_6_pos
  · exact slopeInitialTensorCoefficient_1_7_pos
  · exact slopeInitialTensorCoefficient_1_8_pos
  · exact slopeInitialTensorCoefficient_1_9_pos

theorem slopeInitialTensorCoefficient_row2_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 2 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_2_0_pos
  · exact slopeInitialTensorCoefficient_2_1_pos
  · exact slopeInitialTensorCoefficient_2_2_pos
  · exact slopeInitialTensorCoefficient_2_3_pos
  · exact slopeInitialTensorCoefficient_2_4_pos
  · exact slopeInitialTensorCoefficient_2_5_pos
  · exact slopeInitialTensorCoefficient_2_6_pos
  · exact slopeInitialTensorCoefficient_2_7_pos
  · exact slopeInitialTensorCoefficient_2_8_pos
  · exact slopeInitialTensorCoefficient_2_9_pos

theorem slopeInitialTensorCoefficient_row3_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 3 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_3_0_pos
  · exact slopeInitialTensorCoefficient_3_1_pos
  · exact slopeInitialTensorCoefficient_3_2_pos
  · exact slopeInitialTensorCoefficient_3_3_pos
  · exact slopeInitialTensorCoefficient_3_4_pos
  · exact slopeInitialTensorCoefficient_3_5_pos
  · exact slopeInitialTensorCoefficient_3_6_pos
  · exact slopeInitialTensorCoefficient_3_7_pos
  · exact slopeInitialTensorCoefficient_3_8_pos
  · exact slopeInitialTensorCoefficient_3_9_pos

theorem slopeInitialTensorCoefficient_row4_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 4 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_4_0_pos
  · exact slopeInitialTensorCoefficient_4_1_pos
  · exact slopeInitialTensorCoefficient_4_2_pos
  · exact slopeInitialTensorCoefficient_4_3_pos
  · exact slopeInitialTensorCoefficient_4_4_pos
  · exact slopeInitialTensorCoefficient_4_5_pos
  · exact slopeInitialTensorCoefficient_4_6_pos
  · exact slopeInitialTensorCoefficient_4_7_pos
  · exact slopeInitialTensorCoefficient_4_8_pos
  · exact slopeInitialTensorCoefficient_4_9_pos

theorem slopeInitialTensorCoefficient_row5_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 5 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_5_0_pos
  · exact slopeInitialTensorCoefficient_5_1_pos
  · exact slopeInitialTensorCoefficient_5_2_pos
  · exact slopeInitialTensorCoefficient_5_3_pos
  · exact slopeInitialTensorCoefficient_5_4_pos
  · exact slopeInitialTensorCoefficient_5_5_pos
  · exact slopeInitialTensorCoefficient_5_6_pos
  · exact slopeInitialTensorCoefficient_5_7_pos
  · exact slopeInitialTensorCoefficient_5_8_pos
  · exact slopeInitialTensorCoefficient_5_9_pos

theorem slopeInitialTensorCoefficient_row6_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 6 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_6_0_pos
  · exact slopeInitialTensorCoefficient_6_1_pos
  · exact slopeInitialTensorCoefficient_6_2_pos
  · exact slopeInitialTensorCoefficient_6_3_pos
  · exact slopeInitialTensorCoefficient_6_4_pos
  · exact slopeInitialTensorCoefficient_6_5_pos
  · exact slopeInitialTensorCoefficient_6_6_pos
  · exact slopeInitialTensorCoefficient_6_7_pos
  · exact slopeInitialTensorCoefficient_6_8_pos
  · exact slopeInitialTensorCoefficient_6_9_pos

theorem slopeInitialTensorCoefficient_row7_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 7 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_7_0_pos
  · exact slopeInitialTensorCoefficient_7_1_pos
  · exact slopeInitialTensorCoefficient_7_2_pos
  · exact slopeInitialTensorCoefficient_7_3_pos
  · exact slopeInitialTensorCoefficient_7_4_pos
  · exact slopeInitialTensorCoefficient_7_5_pos
  · exact slopeInitialTensorCoefficient_7_6_pos
  · exact slopeInitialTensorCoefficient_7_7_pos
  · exact slopeInitialTensorCoefficient_7_8_pos
  · exact slopeInitialTensorCoefficient_7_9_pos

theorem slopeInitialTensorCoefficient_row8_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 8 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_8_0_pos
  · exact slopeInitialTensorCoefficient_8_1_pos
  · exact slopeInitialTensorCoefficient_8_2_pos
  · exact slopeInitialTensorCoefficient_8_3_pos
  · exact slopeInitialTensorCoefficient_8_4_pos
  · exact slopeInitialTensorCoefficient_8_5_pos
  · exact slopeInitialTensorCoefficient_8_6_pos
  · exact slopeInitialTensorCoefficient_8_7_pos
  · exact slopeInitialTensorCoefficient_8_8_pos
  · exact slopeInitialTensorCoefficient_8_9_pos

theorem slopeInitialTensorCoefficient_row9_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 9 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_9_0_pos
  · exact slopeInitialTensorCoefficient_9_1_pos
  · exact slopeInitialTensorCoefficient_9_2_pos
  · exact slopeInitialTensorCoefficient_9_3_pos
  · exact slopeInitialTensorCoefficient_9_4_pos
  · exact slopeInitialTensorCoefficient_9_5_pos
  · exact slopeInitialTensorCoefficient_9_6_pos
  · exact slopeInitialTensorCoefficient_9_7_pos
  · exact slopeInitialTensorCoefficient_9_8_pos
  · exact slopeInitialTensorCoefficient_9_9_pos

theorem slopeInitialTensorCoefficient_row10_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 10 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_10_0_pos
  · exact slopeInitialTensorCoefficient_10_1_pos
  · exact slopeInitialTensorCoefficient_10_2_pos
  · exact slopeInitialTensorCoefficient_10_3_pos
  · exact slopeInitialTensorCoefficient_10_4_pos
  · exact slopeInitialTensorCoefficient_10_5_pos
  · exact slopeInitialTensorCoefficient_10_6_pos
  · exact slopeInitialTensorCoefficient_10_7_pos
  · exact slopeInitialTensorCoefficient_10_8_pos
  · exact slopeInitialTensorCoefficient_10_9_pos

theorem slopeInitialTensorCoefficient_row11_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 11 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_11_0_pos
  · exact slopeInitialTensorCoefficient_11_1_pos
  · exact slopeInitialTensorCoefficient_11_2_pos
  · exact slopeInitialTensorCoefficient_11_3_pos
  · exact slopeInitialTensorCoefficient_11_4_pos
  · exact slopeInitialTensorCoefficient_11_5_pos
  · exact slopeInitialTensorCoefficient_11_6_pos
  · exact slopeInitialTensorCoefficient_11_7_pos
  · exact slopeInitialTensorCoefficient_11_8_pos
  · exact slopeInitialTensorCoefficient_11_9_pos

theorem slopeInitialTensorCoefficient_row12_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 12 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_12_0_pos
  · exact slopeInitialTensorCoefficient_12_1_pos
  · exact slopeInitialTensorCoefficient_12_2_pos
  · exact slopeInitialTensorCoefficient_12_3_pos
  · exact slopeInitialTensorCoefficient_12_4_pos
  · exact slopeInitialTensorCoefficient_12_5_pos
  · exact slopeInitialTensorCoefficient_12_6_pos
  · exact slopeInitialTensorCoefficient_12_7_pos
  · exact slopeInitialTensorCoefficient_12_8_pos
  · exact slopeInitialTensorCoefficient_12_9_pos

theorem slopeInitialTensorCoefficient_row13_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 13 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_13_0_pos
  · exact slopeInitialTensorCoefficient_13_1_pos
  · exact slopeInitialTensorCoefficient_13_2_pos
  · exact slopeInitialTensorCoefficient_13_3_pos
  · exact slopeInitialTensorCoefficient_13_4_pos
  · exact slopeInitialTensorCoefficient_13_5_pos
  · exact slopeInitialTensorCoefficient_13_6_pos
  · exact slopeInitialTensorCoefficient_13_7_pos
  · exact slopeInitialTensorCoefficient_13_8_pos
  · exact slopeInitialTensorCoefficient_13_9_pos

theorem slopeInitialTensorCoefficient_row14_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 14 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_14_0_pos
  · exact slopeInitialTensorCoefficient_14_1_pos
  · exact slopeInitialTensorCoefficient_14_2_pos
  · exact slopeInitialTensorCoefficient_14_3_pos
  · exact slopeInitialTensorCoefficient_14_4_pos
  · exact slopeInitialTensorCoefficient_14_5_pos
  · exact slopeInitialTensorCoefficient_14_6_pos
  · exact slopeInitialTensorCoefficient_14_7_pos
  · exact slopeInitialTensorCoefficient_14_8_pos
  · exact slopeInitialTensorCoefficient_14_9_pos

theorem slopeInitialTensorCoefficient_row15_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 15 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_15_0_pos
  · exact slopeInitialTensorCoefficient_15_1_pos
  · exact slopeInitialTensorCoefficient_15_2_pos
  · exact slopeInitialTensorCoefficient_15_3_pos
  · exact slopeInitialTensorCoefficient_15_4_pos
  · exact slopeInitialTensorCoefficient_15_5_pos
  · exact slopeInitialTensorCoefficient_15_6_pos
  · exact slopeInitialTensorCoefficient_15_7_pos
  · exact slopeInitialTensorCoefficient_15_8_pos
  · exact slopeInitialTensorCoefficient_15_9_pos

theorem slopeInitialTensorCoefficient_row16_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 16 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_16_0_pos
  · exact slopeInitialTensorCoefficient_16_1_pos
  · exact slopeInitialTensorCoefficient_16_2_pos
  · exact slopeInitialTensorCoefficient_16_3_pos
  · exact slopeInitialTensorCoefficient_16_4_pos
  · exact slopeInitialTensorCoefficient_16_5_pos
  · exact slopeInitialTensorCoefficient_16_6_pos
  · exact slopeInitialTensorCoefficient_16_7_pos
  · exact slopeInitialTensorCoefficient_16_8_pos
  · exact slopeInitialTensorCoefficient_16_9_pos

theorem slopeInitialTensorCoefficient_row17_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 17 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_17_0_pos
  · exact slopeInitialTensorCoefficient_17_1_pos
  · exact slopeInitialTensorCoefficient_17_2_pos
  · exact slopeInitialTensorCoefficient_17_3_pos
  · exact slopeInitialTensorCoefficient_17_4_pos
  · exact slopeInitialTensorCoefficient_17_5_pos
  · exact slopeInitialTensorCoefficient_17_6_pos
  · exact slopeInitialTensorCoefficient_17_7_pos
  · exact slopeInitialTensorCoefficient_17_8_pos
  · exact slopeInitialTensorCoefficient_17_9_pos

theorem slopeInitialTensorCoefficient_row18_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 18 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_18_0_pos
  · exact slopeInitialTensorCoefficient_18_1_pos
  · exact slopeInitialTensorCoefficient_18_2_pos
  · exact slopeInitialTensorCoefficient_18_3_pos
  · exact slopeInitialTensorCoefficient_18_4_pos
  · exact slopeInitialTensorCoefficient_18_5_pos
  · exact slopeInitialTensorCoefficient_18_6_pos
  · exact slopeInitialTensorCoefficient_18_7_pos
  · exact slopeInitialTensorCoefficient_18_8_pos
  · exact slopeInitialTensorCoefficient_18_9_pos

theorem slopeInitialTensorCoefficient_row19_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 19 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_19_0_pos
  · exact slopeInitialTensorCoefficient_19_1_pos
  · exact slopeInitialTensorCoefficient_19_2_pos
  · exact slopeInitialTensorCoefficient_19_3_pos
  · exact slopeInitialTensorCoefficient_19_4_pos
  · exact slopeInitialTensorCoefficient_19_5_pos
  · exact slopeInitialTensorCoefficient_19_6_pos
  · exact slopeInitialTensorCoefficient_19_7_pos
  · exact slopeInitialTensorCoefficient_19_8_pos
  · exact slopeInitialTensorCoefficient_19_9_pos

theorem slopeInitialTensorCoefficient_row20_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 20 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_20_0_pos
  · exact slopeInitialTensorCoefficient_20_1_pos
  · exact slopeInitialTensorCoefficient_20_2_pos
  · exact slopeInitialTensorCoefficient_20_3_pos
  · exact slopeInitialTensorCoefficient_20_4_pos
  · exact slopeInitialTensorCoefficient_20_5_pos
  · exact slopeInitialTensorCoefficient_20_6_pos
  · exact slopeInitialTensorCoefficient_20_7_pos
  · exact slopeInitialTensorCoefficient_20_8_pos
  · exact slopeInitialTensorCoefficient_20_9_pos

theorem slopeInitialTensorCoefficient_row21_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 21 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_21_0_pos
  · exact slopeInitialTensorCoefficient_21_1_pos
  · exact slopeInitialTensorCoefficient_21_2_pos
  · exact slopeInitialTensorCoefficient_21_3_pos
  · exact slopeInitialTensorCoefficient_21_4_pos
  · exact slopeInitialTensorCoefficient_21_5_pos
  · exact slopeInitialTensorCoefficient_21_6_pos
  · exact slopeInitialTensorCoefficient_21_7_pos
  · exact slopeInitialTensorCoefficient_21_8_pos
  · exact slopeInitialTensorCoefficient_21_9_pos

theorem slopeInitialTensorCoefficient_row22_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 22 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_22_0_pos
  · exact slopeInitialTensorCoefficient_22_1_pos
  · exact slopeInitialTensorCoefficient_22_2_pos
  · exact slopeInitialTensorCoefficient_22_3_pos
  · exact slopeInitialTensorCoefficient_22_4_pos
  · exact slopeInitialTensorCoefficient_22_5_pos
  · exact slopeInitialTensorCoefficient_22_6_pos
  · exact slopeInitialTensorCoefficient_22_7_pos
  · exact slopeInitialTensorCoefficient_22_8_pos
  · exact slopeInitialTensorCoefficient_22_9_pos

theorem slopeInitialTensorCoefficient_row23_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 23 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_23_0_pos
  · exact slopeInitialTensorCoefficient_23_1_pos
  · exact slopeInitialTensorCoefficient_23_2_pos
  · exact slopeInitialTensorCoefficient_23_3_pos
  · exact slopeInitialTensorCoefficient_23_4_pos
  · exact slopeInitialTensorCoefficient_23_5_pos
  · exact slopeInitialTensorCoefficient_23_6_pos
  · exact slopeInitialTensorCoefficient_23_7_pos
  · exact slopeInitialTensorCoefficient_23_8_pos
  · exact slopeInitialTensorCoefficient_23_9_pos

theorem slopeInitialTensorCoefficient_row24_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 24 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_24_0_pos
  · exact slopeInitialTensorCoefficient_24_1_pos
  · exact slopeInitialTensorCoefficient_24_2_pos
  · exact slopeInitialTensorCoefficient_24_3_pos
  · exact slopeInitialTensorCoefficient_24_4_pos
  · exact slopeInitialTensorCoefficient_24_5_pos
  · exact slopeInitialTensorCoefficient_24_6_pos
  · exact slopeInitialTensorCoefficient_24_7_pos
  · exact slopeInitialTensorCoefficient_24_8_pos
  · exact slopeInitialTensorCoefficient_24_9_pos

theorem slopeInitialTensorCoefficient_row25_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 25 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_25_0_pos
  · exact slopeInitialTensorCoefficient_25_1_pos
  · exact slopeInitialTensorCoefficient_25_2_pos
  · exact slopeInitialTensorCoefficient_25_3_pos
  · exact slopeInitialTensorCoefficient_25_4_pos
  · exact slopeInitialTensorCoefficient_25_5_pos
  · exact slopeInitialTensorCoefficient_25_6_pos
  · exact slopeInitialTensorCoefficient_25_7_pos
  · exact slopeInitialTensorCoefficient_25_8_pos
  · exact slopeInitialTensorCoefficient_25_9_pos

theorem slopeInitialTensorCoefficient_row26_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 26 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_26_0_pos
  · exact slopeInitialTensorCoefficient_26_1_pos
  · exact slopeInitialTensorCoefficient_26_2_pos
  · exact slopeInitialTensorCoefficient_26_3_pos
  · exact slopeInitialTensorCoefficient_26_4_pos
  · exact slopeInitialTensorCoefficient_26_5_pos
  · exact slopeInitialTensorCoefficient_26_6_pos
  · exact slopeInitialTensorCoefficient_26_7_pos
  · exact slopeInitialTensorCoefficient_26_8_pos
  · exact slopeInitialTensorCoefficient_26_9_pos

theorem slopeInitialTensorCoefficient_row27_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 27 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_27_0_pos
  · exact slopeInitialTensorCoefficient_27_1_pos
  · exact slopeInitialTensorCoefficient_27_2_pos
  · exact slopeInitialTensorCoefficient_27_3_pos
  · exact slopeInitialTensorCoefficient_27_4_pos
  · exact slopeInitialTensorCoefficient_27_5_pos
  · exact slopeInitialTensorCoefficient_27_6_pos
  · exact slopeInitialTensorCoefficient_27_7_pos
  · exact slopeInitialTensorCoefficient_27_8_pos
  · exact slopeInitialTensorCoefficient_27_9_pos

theorem slopeInitialTensorCoefficient_row28_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 28 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_28_0_pos
  · exact slopeInitialTensorCoefficient_28_1_pos
  · exact slopeInitialTensorCoefficient_28_2_pos
  · exact slopeInitialTensorCoefficient_28_3_pos
  · exact slopeInitialTensorCoefficient_28_4_pos
  · exact slopeInitialTensorCoefficient_28_5_pos
  · exact slopeInitialTensorCoefficient_28_6_pos
  · exact slopeInitialTensorCoefficient_28_7_pos
  · exact slopeInitialTensorCoefficient_28_8_pos
  · exact slopeInitialTensorCoefficient_28_9_pos

theorem slopeInitialTensorCoefficient_row29_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 29 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_29_0_pos
  · exact slopeInitialTensorCoefficient_29_1_pos
  · exact slopeInitialTensorCoefficient_29_2_pos
  · exact slopeInitialTensorCoefficient_29_3_pos
  · exact slopeInitialTensorCoefficient_29_4_pos
  · exact slopeInitialTensorCoefficient_29_5_pos
  · exact slopeInitialTensorCoefficient_29_6_pos
  · exact slopeInitialTensorCoefficient_29_7_pos
  · exact slopeInitialTensorCoefficient_29_8_pos
  · exact slopeInitialTensorCoefficient_29_9_pos

theorem slopeInitialTensorCoefficient_row30_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 30 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_30_0_pos
  · exact slopeInitialTensorCoefficient_30_1_pos
  · exact slopeInitialTensorCoefficient_30_2_pos
  · exact slopeInitialTensorCoefficient_30_3_pos
  · exact slopeInitialTensorCoefficient_30_4_pos
  · exact slopeInitialTensorCoefficient_30_5_pos
  · exact slopeInitialTensorCoefficient_30_6_pos
  · exact slopeInitialTensorCoefficient_30_7_pos
  · exact slopeInitialTensorCoefficient_30_8_pos
  · exact slopeInitialTensorCoefficient_30_9_pos

theorem slopeInitialTensorCoefficient_row31_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 31 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_31_0_pos
  · exact slopeInitialTensorCoefficient_31_1_pos
  · exact slopeInitialTensorCoefficient_31_2_pos
  · exact slopeInitialTensorCoefficient_31_3_pos
  · exact slopeInitialTensorCoefficient_31_4_pos
  · exact slopeInitialTensorCoefficient_31_5_pos
  · exact slopeInitialTensorCoefficient_31_6_pos
  · exact slopeInitialTensorCoefficient_31_7_pos
  · exact slopeInitialTensorCoefficient_31_8_pos
  · exact slopeInitialTensorCoefficient_31_9_pos

theorem slopeInitialTensorCoefficient_row32_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 32 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_32_0_pos
  · exact slopeInitialTensorCoefficient_32_1_pos
  · exact slopeInitialTensorCoefficient_32_2_pos
  · exact slopeInitialTensorCoefficient_32_3_pos
  · exact slopeInitialTensorCoefficient_32_4_pos
  · exact slopeInitialTensorCoefficient_32_5_pos
  · exact slopeInitialTensorCoefficient_32_6_pos
  · exact slopeInitialTensorCoefficient_32_7_pos
  · exact slopeInitialTensorCoefficient_32_8_pos
  · exact slopeInitialTensorCoefficient_32_9_pos

theorem slopeInitialTensorCoefficient_row33_pos (B : Fin 10) :
    0 < slopeInitialTensorCoefficient 33 B := by
  fin_cases B
  · exact slopeInitialTensorCoefficient_33_0_pos
  · exact slopeInitialTensorCoefficient_33_1_pos
  · exact slopeInitialTensorCoefficient_33_2_pos
  · exact slopeInitialTensorCoefficient_33_3_pos
  · exact slopeInitialTensorCoefficient_33_4_pos
  · exact slopeInitialTensorCoefficient_33_5_pos
  · exact slopeInitialTensorCoefficient_33_6_pos
  · exact slopeInitialTensorCoefficient_33_7_pos
  · exact slopeInitialTensorCoefficient_33_8_pos
  · exact slopeInitialTensorCoefficient_33_9_pos

theorem slopeInitialTensorCoefficient_pos (A : Fin 34) (B : Fin 10) :
    0 < slopeInitialTensorCoefficient A B := by
  fin_cases A
  · exact slopeInitialTensorCoefficient_row0_pos B
  · exact slopeInitialTensorCoefficient_row1_pos B
  · exact slopeInitialTensorCoefficient_row2_pos B
  · exact slopeInitialTensorCoefficient_row3_pos B
  · exact slopeInitialTensorCoefficient_row4_pos B
  · exact slopeInitialTensorCoefficient_row5_pos B
  · exact slopeInitialTensorCoefficient_row6_pos B
  · exact slopeInitialTensorCoefficient_row7_pos B
  · exact slopeInitialTensorCoefficient_row8_pos B
  · exact slopeInitialTensorCoefficient_row9_pos B
  · exact slopeInitialTensorCoefficient_row10_pos B
  · exact slopeInitialTensorCoefficient_row11_pos B
  · exact slopeInitialTensorCoefficient_row12_pos B
  · exact slopeInitialTensorCoefficient_row13_pos B
  · exact slopeInitialTensorCoefficient_row14_pos B
  · exact slopeInitialTensorCoefficient_row15_pos B
  · exact slopeInitialTensorCoefficient_row16_pos B
  · exact slopeInitialTensorCoefficient_row17_pos B
  · exact slopeInitialTensorCoefficient_row18_pos B
  · exact slopeInitialTensorCoefficient_row19_pos B
  · exact slopeInitialTensorCoefficient_row20_pos B
  · exact slopeInitialTensorCoefficient_row21_pos B
  · exact slopeInitialTensorCoefficient_row22_pos B
  · exact slopeInitialTensorCoefficient_row23_pos B
  · exact slopeInitialTensorCoefficient_row24_pos B
  · exact slopeInitialTensorCoefficient_row25_pos B
  · exact slopeInitialTensorCoefficient_row26_pos B
  · exact slopeInitialTensorCoefficient_row27_pos B
  · exact slopeInitialTensorCoefficient_row28_pos B
  · exact slopeInitialTensorCoefficient_row29_pos B
  · exact slopeInitialTensorCoefficient_row30_pos B
  · exact slopeInitialTensorCoefficient_row31_pos B
  · exact slopeInitialTensorCoefficient_row32_pos B
  · exact slopeInitialTensorCoefficient_row33_pos B

theorem slopeInitialQuotient_unit_pos (t v : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < slopeInitialQuotient ((4/5)*t) ((361/25)*v) := by
  rw [←slopeInitialTensorValue_reconstruction]
  apply kineticBernstein_pos 33 _ t _ ht0 ht1
  intro A hA
  apply kineticBernstein_pos 9 _ v _ hv0 hv1
  intro B hB
  exact slopeInitialTensorCoefficient_pos ⟨A,hA⟩ ⟨B,hB⟩

theorem slopeInitialQuotient_pos (h r : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 4/5) (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    0 < slopeInitialQuotient h r := by
  have ht0 : 0 ≤ h/(4/5:ℝ) := div_nonneg hh0 (by norm_num)
  have ht1 : h/(4/5:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hh1)
  have hv0 : 0 ≤ r/(361/25:ℝ) := div_nonneg hr0 (by norm_num)
  have hv1 : r/(361/25:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hr1)
  have hp := slopeInitialQuotient_unit_pos (h/(4/5)) (r/(361/25)) ht0 ht1 hv0 hv1
  have he : (4/5:ℝ)*(h/(4/5))=h := by ring
  have re : (361/25:ℝ)*(r/(361/25))=r := by ring
  simpa only [he,re] using hp

theorem reducedKineticValue_initial_deriv_neg (h r : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 4/5) (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    deriv (reducedKineticValue h (9-r*h^2)) 0 < 0 := by
  have hp := mul_pos (pow_pos hh0 5) (slopeInitialQuotient_pos h r hh0.le hh1 hr0 hr1)
  rw [←slopeInitial_factor,negKineticSlopeControl_zero] at hp
  rw [reducedKineticValue_zero_deriv]
  exact neg_pos.mp hp

end
end HTGeometry.ThetaRatioKineticContraction

