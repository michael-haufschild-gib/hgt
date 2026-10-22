import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8Reconstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow0
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow5
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow6
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow7
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow8
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow9
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow10
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow11
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow12
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow13
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow14
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow15
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow16
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow17
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow18
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow19
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow20
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow21
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow22
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow23
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow24
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow25
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow26
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow27
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow28
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow29
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow30
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow31
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow32
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow33
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow34
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow35
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow36
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow37
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeInterior8TensorRow38
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein

theorem slopeInterior8TensorCoefficient_row0_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 0 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_0_0_pos
  · exact slopeInterior8TensorCoefficient_0_1_pos
  · exact slopeInterior8TensorCoefficient_0_2_pos
  · exact slopeInterior8TensorCoefficient_0_3_pos
  · exact slopeInterior8TensorCoefficient_0_4_pos
  · exact slopeInterior8TensorCoefficient_0_5_pos
  · exact slopeInterior8TensorCoefficient_0_6_pos
  · exact slopeInterior8TensorCoefficient_0_7_pos
  · exact slopeInterior8TensorCoefficient_0_8_pos
  · exact slopeInterior8TensorCoefficient_0_9_pos

theorem slopeInterior8TensorCoefficient_row1_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 1 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_1_0_pos
  · exact slopeInterior8TensorCoefficient_1_1_pos
  · exact slopeInterior8TensorCoefficient_1_2_pos
  · exact slopeInterior8TensorCoefficient_1_3_pos
  · exact slopeInterior8TensorCoefficient_1_4_pos
  · exact slopeInterior8TensorCoefficient_1_5_pos
  · exact slopeInterior8TensorCoefficient_1_6_pos
  · exact slopeInterior8TensorCoefficient_1_7_pos
  · exact slopeInterior8TensorCoefficient_1_8_pos
  · exact slopeInterior8TensorCoefficient_1_9_pos

theorem slopeInterior8TensorCoefficient_row2_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 2 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_2_0_pos
  · exact slopeInterior8TensorCoefficient_2_1_pos
  · exact slopeInterior8TensorCoefficient_2_2_pos
  · exact slopeInterior8TensorCoefficient_2_3_pos
  · exact slopeInterior8TensorCoefficient_2_4_pos
  · exact slopeInterior8TensorCoefficient_2_5_pos
  · exact slopeInterior8TensorCoefficient_2_6_pos
  · exact slopeInterior8TensorCoefficient_2_7_pos
  · exact slopeInterior8TensorCoefficient_2_8_pos
  · exact slopeInterior8TensorCoefficient_2_9_pos

theorem slopeInterior8TensorCoefficient_row3_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 3 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_3_0_pos
  · exact slopeInterior8TensorCoefficient_3_1_pos
  · exact slopeInterior8TensorCoefficient_3_2_pos
  · exact slopeInterior8TensorCoefficient_3_3_pos
  · exact slopeInterior8TensorCoefficient_3_4_pos
  · exact slopeInterior8TensorCoefficient_3_5_pos
  · exact slopeInterior8TensorCoefficient_3_6_pos
  · exact slopeInterior8TensorCoefficient_3_7_pos
  · exact slopeInterior8TensorCoefficient_3_8_pos
  · exact slopeInterior8TensorCoefficient_3_9_pos

theorem slopeInterior8TensorCoefficient_row4_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 4 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_4_0_pos
  · exact slopeInterior8TensorCoefficient_4_1_pos
  · exact slopeInterior8TensorCoefficient_4_2_pos
  · exact slopeInterior8TensorCoefficient_4_3_pos
  · exact slopeInterior8TensorCoefficient_4_4_pos
  · exact slopeInterior8TensorCoefficient_4_5_pos
  · exact slopeInterior8TensorCoefficient_4_6_pos
  · exact slopeInterior8TensorCoefficient_4_7_pos
  · exact slopeInterior8TensorCoefficient_4_8_pos
  · exact slopeInterior8TensorCoefficient_4_9_pos

theorem slopeInterior8TensorCoefficient_row5_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 5 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_5_0_pos
  · exact slopeInterior8TensorCoefficient_5_1_pos
  · exact slopeInterior8TensorCoefficient_5_2_pos
  · exact slopeInterior8TensorCoefficient_5_3_pos
  · exact slopeInterior8TensorCoefficient_5_4_pos
  · exact slopeInterior8TensorCoefficient_5_5_pos
  · exact slopeInterior8TensorCoefficient_5_6_pos
  · exact slopeInterior8TensorCoefficient_5_7_pos
  · exact slopeInterior8TensorCoefficient_5_8_pos
  · exact slopeInterior8TensorCoefficient_5_9_pos

theorem slopeInterior8TensorCoefficient_row6_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 6 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_6_0_pos
  · exact slopeInterior8TensorCoefficient_6_1_pos
  · exact slopeInterior8TensorCoefficient_6_2_pos
  · exact slopeInterior8TensorCoefficient_6_3_pos
  · exact slopeInterior8TensorCoefficient_6_4_pos
  · exact slopeInterior8TensorCoefficient_6_5_pos
  · exact slopeInterior8TensorCoefficient_6_6_pos
  · exact slopeInterior8TensorCoefficient_6_7_pos
  · exact slopeInterior8TensorCoefficient_6_8_pos
  · exact slopeInterior8TensorCoefficient_6_9_pos

theorem slopeInterior8TensorCoefficient_row7_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 7 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_7_0_pos
  · exact slopeInterior8TensorCoefficient_7_1_pos
  · exact slopeInterior8TensorCoefficient_7_2_pos
  · exact slopeInterior8TensorCoefficient_7_3_pos
  · exact slopeInterior8TensorCoefficient_7_4_pos
  · exact slopeInterior8TensorCoefficient_7_5_pos
  · exact slopeInterior8TensorCoefficient_7_6_pos
  · exact slopeInterior8TensorCoefficient_7_7_pos
  · exact slopeInterior8TensorCoefficient_7_8_pos
  · exact slopeInterior8TensorCoefficient_7_9_pos

theorem slopeInterior8TensorCoefficient_row8_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 8 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_8_0_pos
  · exact slopeInterior8TensorCoefficient_8_1_pos
  · exact slopeInterior8TensorCoefficient_8_2_pos
  · exact slopeInterior8TensorCoefficient_8_3_pos
  · exact slopeInterior8TensorCoefficient_8_4_pos
  · exact slopeInterior8TensorCoefficient_8_5_pos
  · exact slopeInterior8TensorCoefficient_8_6_pos
  · exact slopeInterior8TensorCoefficient_8_7_pos
  · exact slopeInterior8TensorCoefficient_8_8_pos
  · exact slopeInterior8TensorCoefficient_8_9_pos

theorem slopeInterior8TensorCoefficient_row9_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 9 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_9_0_pos
  · exact slopeInterior8TensorCoefficient_9_1_pos
  · exact slopeInterior8TensorCoefficient_9_2_pos
  · exact slopeInterior8TensorCoefficient_9_3_pos
  · exact slopeInterior8TensorCoefficient_9_4_pos
  · exact slopeInterior8TensorCoefficient_9_5_pos
  · exact slopeInterior8TensorCoefficient_9_6_pos
  · exact slopeInterior8TensorCoefficient_9_7_pos
  · exact slopeInterior8TensorCoefficient_9_8_pos
  · exact slopeInterior8TensorCoefficient_9_9_pos

theorem slopeInterior8TensorCoefficient_row10_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 10 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_10_0_pos
  · exact slopeInterior8TensorCoefficient_10_1_pos
  · exact slopeInterior8TensorCoefficient_10_2_pos
  · exact slopeInterior8TensorCoefficient_10_3_pos
  · exact slopeInterior8TensorCoefficient_10_4_pos
  · exact slopeInterior8TensorCoefficient_10_5_pos
  · exact slopeInterior8TensorCoefficient_10_6_pos
  · exact slopeInterior8TensorCoefficient_10_7_pos
  · exact slopeInterior8TensorCoefficient_10_8_pos
  · exact slopeInterior8TensorCoefficient_10_9_pos

theorem slopeInterior8TensorCoefficient_row11_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 11 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_11_0_pos
  · exact slopeInterior8TensorCoefficient_11_1_pos
  · exact slopeInterior8TensorCoefficient_11_2_pos
  · exact slopeInterior8TensorCoefficient_11_3_pos
  · exact slopeInterior8TensorCoefficient_11_4_pos
  · exact slopeInterior8TensorCoefficient_11_5_pos
  · exact slopeInterior8TensorCoefficient_11_6_pos
  · exact slopeInterior8TensorCoefficient_11_7_pos
  · exact slopeInterior8TensorCoefficient_11_8_pos
  · exact slopeInterior8TensorCoefficient_11_9_pos

theorem slopeInterior8TensorCoefficient_row12_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 12 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_12_0_pos
  · exact slopeInterior8TensorCoefficient_12_1_pos
  · exact slopeInterior8TensorCoefficient_12_2_pos
  · exact slopeInterior8TensorCoefficient_12_3_pos
  · exact slopeInterior8TensorCoefficient_12_4_pos
  · exact slopeInterior8TensorCoefficient_12_5_pos
  · exact slopeInterior8TensorCoefficient_12_6_pos
  · exact slopeInterior8TensorCoefficient_12_7_pos
  · exact slopeInterior8TensorCoefficient_12_8_pos
  · exact slopeInterior8TensorCoefficient_12_9_pos

theorem slopeInterior8TensorCoefficient_row13_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 13 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_13_0_pos
  · exact slopeInterior8TensorCoefficient_13_1_pos
  · exact slopeInterior8TensorCoefficient_13_2_pos
  · exact slopeInterior8TensorCoefficient_13_3_pos
  · exact slopeInterior8TensorCoefficient_13_4_pos
  · exact slopeInterior8TensorCoefficient_13_5_pos
  · exact slopeInterior8TensorCoefficient_13_6_pos
  · exact slopeInterior8TensorCoefficient_13_7_pos
  · exact slopeInterior8TensorCoefficient_13_8_pos
  · exact slopeInterior8TensorCoefficient_13_9_pos

theorem slopeInterior8TensorCoefficient_row14_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 14 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_14_0_pos
  · exact slopeInterior8TensorCoefficient_14_1_pos
  · exact slopeInterior8TensorCoefficient_14_2_pos
  · exact slopeInterior8TensorCoefficient_14_3_pos
  · exact slopeInterior8TensorCoefficient_14_4_pos
  · exact slopeInterior8TensorCoefficient_14_5_pos
  · exact slopeInterior8TensorCoefficient_14_6_pos
  · exact slopeInterior8TensorCoefficient_14_7_pos
  · exact slopeInterior8TensorCoefficient_14_8_pos
  · exact slopeInterior8TensorCoefficient_14_9_pos

theorem slopeInterior8TensorCoefficient_row15_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 15 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_15_0_pos
  · exact slopeInterior8TensorCoefficient_15_1_pos
  · exact slopeInterior8TensorCoefficient_15_2_pos
  · exact slopeInterior8TensorCoefficient_15_3_pos
  · exact slopeInterior8TensorCoefficient_15_4_pos
  · exact slopeInterior8TensorCoefficient_15_5_pos
  · exact slopeInterior8TensorCoefficient_15_6_pos
  · exact slopeInterior8TensorCoefficient_15_7_pos
  · exact slopeInterior8TensorCoefficient_15_8_pos
  · exact slopeInterior8TensorCoefficient_15_9_pos

theorem slopeInterior8TensorCoefficient_row16_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 16 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_16_0_pos
  · exact slopeInterior8TensorCoefficient_16_1_pos
  · exact slopeInterior8TensorCoefficient_16_2_pos
  · exact slopeInterior8TensorCoefficient_16_3_pos
  · exact slopeInterior8TensorCoefficient_16_4_pos
  · exact slopeInterior8TensorCoefficient_16_5_pos
  · exact slopeInterior8TensorCoefficient_16_6_pos
  · exact slopeInterior8TensorCoefficient_16_7_pos
  · exact slopeInterior8TensorCoefficient_16_8_pos
  · exact slopeInterior8TensorCoefficient_16_9_pos

theorem slopeInterior8TensorCoefficient_row17_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 17 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_17_0_pos
  · exact slopeInterior8TensorCoefficient_17_1_pos
  · exact slopeInterior8TensorCoefficient_17_2_pos
  · exact slopeInterior8TensorCoefficient_17_3_pos
  · exact slopeInterior8TensorCoefficient_17_4_pos
  · exact slopeInterior8TensorCoefficient_17_5_pos
  · exact slopeInterior8TensorCoefficient_17_6_pos
  · exact slopeInterior8TensorCoefficient_17_7_pos
  · exact slopeInterior8TensorCoefficient_17_8_pos
  · exact slopeInterior8TensorCoefficient_17_9_pos

theorem slopeInterior8TensorCoefficient_row18_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 18 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_18_0_pos
  · exact slopeInterior8TensorCoefficient_18_1_pos
  · exact slopeInterior8TensorCoefficient_18_2_pos
  · exact slopeInterior8TensorCoefficient_18_3_pos
  · exact slopeInterior8TensorCoefficient_18_4_pos
  · exact slopeInterior8TensorCoefficient_18_5_pos
  · exact slopeInterior8TensorCoefficient_18_6_pos
  · exact slopeInterior8TensorCoefficient_18_7_pos
  · exact slopeInterior8TensorCoefficient_18_8_pos
  · exact slopeInterior8TensorCoefficient_18_9_pos

theorem slopeInterior8TensorCoefficient_row19_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 19 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_19_0_pos
  · exact slopeInterior8TensorCoefficient_19_1_pos
  · exact slopeInterior8TensorCoefficient_19_2_pos
  · exact slopeInterior8TensorCoefficient_19_3_pos
  · exact slopeInterior8TensorCoefficient_19_4_pos
  · exact slopeInterior8TensorCoefficient_19_5_pos
  · exact slopeInterior8TensorCoefficient_19_6_pos
  · exact slopeInterior8TensorCoefficient_19_7_pos
  · exact slopeInterior8TensorCoefficient_19_8_pos
  · exact slopeInterior8TensorCoefficient_19_9_pos

theorem slopeInterior8TensorCoefficient_row20_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 20 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_20_0_pos
  · exact slopeInterior8TensorCoefficient_20_1_pos
  · exact slopeInterior8TensorCoefficient_20_2_pos
  · exact slopeInterior8TensorCoefficient_20_3_pos
  · exact slopeInterior8TensorCoefficient_20_4_pos
  · exact slopeInterior8TensorCoefficient_20_5_pos
  · exact slopeInterior8TensorCoefficient_20_6_pos
  · exact slopeInterior8TensorCoefficient_20_7_pos
  · exact slopeInterior8TensorCoefficient_20_8_pos
  · exact slopeInterior8TensorCoefficient_20_9_pos

theorem slopeInterior8TensorCoefficient_row21_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 21 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_21_0_pos
  · exact slopeInterior8TensorCoefficient_21_1_pos
  · exact slopeInterior8TensorCoefficient_21_2_pos
  · exact slopeInterior8TensorCoefficient_21_3_pos
  · exact slopeInterior8TensorCoefficient_21_4_pos
  · exact slopeInterior8TensorCoefficient_21_5_pos
  · exact slopeInterior8TensorCoefficient_21_6_pos
  · exact slopeInterior8TensorCoefficient_21_7_pos
  · exact slopeInterior8TensorCoefficient_21_8_pos
  · exact slopeInterior8TensorCoefficient_21_9_pos

theorem slopeInterior8TensorCoefficient_row22_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 22 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_22_0_pos
  · exact slopeInterior8TensorCoefficient_22_1_pos
  · exact slopeInterior8TensorCoefficient_22_2_pos
  · exact slopeInterior8TensorCoefficient_22_3_pos
  · exact slopeInterior8TensorCoefficient_22_4_pos
  · exact slopeInterior8TensorCoefficient_22_5_pos
  · exact slopeInterior8TensorCoefficient_22_6_pos
  · exact slopeInterior8TensorCoefficient_22_7_pos
  · exact slopeInterior8TensorCoefficient_22_8_pos
  · exact slopeInterior8TensorCoefficient_22_9_pos

theorem slopeInterior8TensorCoefficient_row23_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 23 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_23_0_pos
  · exact slopeInterior8TensorCoefficient_23_1_pos
  · exact slopeInterior8TensorCoefficient_23_2_pos
  · exact slopeInterior8TensorCoefficient_23_3_pos
  · exact slopeInterior8TensorCoefficient_23_4_pos
  · exact slopeInterior8TensorCoefficient_23_5_pos
  · exact slopeInterior8TensorCoefficient_23_6_pos
  · exact slopeInterior8TensorCoefficient_23_7_pos
  · exact slopeInterior8TensorCoefficient_23_8_pos
  · exact slopeInterior8TensorCoefficient_23_9_pos

theorem slopeInterior8TensorCoefficient_row24_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 24 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_24_0_pos
  · exact slopeInterior8TensorCoefficient_24_1_pos
  · exact slopeInterior8TensorCoefficient_24_2_pos
  · exact slopeInterior8TensorCoefficient_24_3_pos
  · exact slopeInterior8TensorCoefficient_24_4_pos
  · exact slopeInterior8TensorCoefficient_24_5_pos
  · exact slopeInterior8TensorCoefficient_24_6_pos
  · exact slopeInterior8TensorCoefficient_24_7_pos
  · exact slopeInterior8TensorCoefficient_24_8_pos
  · exact slopeInterior8TensorCoefficient_24_9_pos

theorem slopeInterior8TensorCoefficient_row25_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 25 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_25_0_pos
  · exact slopeInterior8TensorCoefficient_25_1_pos
  · exact slopeInterior8TensorCoefficient_25_2_pos
  · exact slopeInterior8TensorCoefficient_25_3_pos
  · exact slopeInterior8TensorCoefficient_25_4_pos
  · exact slopeInterior8TensorCoefficient_25_5_pos
  · exact slopeInterior8TensorCoefficient_25_6_pos
  · exact slopeInterior8TensorCoefficient_25_7_pos
  · exact slopeInterior8TensorCoefficient_25_8_pos
  · exact slopeInterior8TensorCoefficient_25_9_pos

theorem slopeInterior8TensorCoefficient_row26_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 26 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_26_0_pos
  · exact slopeInterior8TensorCoefficient_26_1_pos
  · exact slopeInterior8TensorCoefficient_26_2_pos
  · exact slopeInterior8TensorCoefficient_26_3_pos
  · exact slopeInterior8TensorCoefficient_26_4_pos
  · exact slopeInterior8TensorCoefficient_26_5_pos
  · exact slopeInterior8TensorCoefficient_26_6_pos
  · exact slopeInterior8TensorCoefficient_26_7_pos
  · exact slopeInterior8TensorCoefficient_26_8_pos
  · exact slopeInterior8TensorCoefficient_26_9_pos

theorem slopeInterior8TensorCoefficient_row27_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 27 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_27_0_pos
  · exact slopeInterior8TensorCoefficient_27_1_pos
  · exact slopeInterior8TensorCoefficient_27_2_pos
  · exact slopeInterior8TensorCoefficient_27_3_pos
  · exact slopeInterior8TensorCoefficient_27_4_pos
  · exact slopeInterior8TensorCoefficient_27_5_pos
  · exact slopeInterior8TensorCoefficient_27_6_pos
  · exact slopeInterior8TensorCoefficient_27_7_pos
  · exact slopeInterior8TensorCoefficient_27_8_pos
  · exact slopeInterior8TensorCoefficient_27_9_pos

theorem slopeInterior8TensorCoefficient_row28_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 28 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_28_0_pos
  · exact slopeInterior8TensorCoefficient_28_1_pos
  · exact slopeInterior8TensorCoefficient_28_2_pos
  · exact slopeInterior8TensorCoefficient_28_3_pos
  · exact slopeInterior8TensorCoefficient_28_4_pos
  · exact slopeInterior8TensorCoefficient_28_5_pos
  · exact slopeInterior8TensorCoefficient_28_6_pos
  · exact slopeInterior8TensorCoefficient_28_7_pos
  · exact slopeInterior8TensorCoefficient_28_8_pos
  · exact slopeInterior8TensorCoefficient_28_9_pos

theorem slopeInterior8TensorCoefficient_row29_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 29 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_29_0_pos
  · exact slopeInterior8TensorCoefficient_29_1_pos
  · exact slopeInterior8TensorCoefficient_29_2_pos
  · exact slopeInterior8TensorCoefficient_29_3_pos
  · exact slopeInterior8TensorCoefficient_29_4_pos
  · exact slopeInterior8TensorCoefficient_29_5_pos
  · exact slopeInterior8TensorCoefficient_29_6_pos
  · exact slopeInterior8TensorCoefficient_29_7_pos
  · exact slopeInterior8TensorCoefficient_29_8_pos
  · exact slopeInterior8TensorCoefficient_29_9_pos

theorem slopeInterior8TensorCoefficient_row30_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 30 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_30_0_pos
  · exact slopeInterior8TensorCoefficient_30_1_pos
  · exact slopeInterior8TensorCoefficient_30_2_pos
  · exact slopeInterior8TensorCoefficient_30_3_pos
  · exact slopeInterior8TensorCoefficient_30_4_pos
  · exact slopeInterior8TensorCoefficient_30_5_pos
  · exact slopeInterior8TensorCoefficient_30_6_pos
  · exact slopeInterior8TensorCoefficient_30_7_pos
  · exact slopeInterior8TensorCoefficient_30_8_pos
  · exact slopeInterior8TensorCoefficient_30_9_pos

theorem slopeInterior8TensorCoefficient_row31_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 31 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_31_0_pos
  · exact slopeInterior8TensorCoefficient_31_1_pos
  · exact slopeInterior8TensorCoefficient_31_2_pos
  · exact slopeInterior8TensorCoefficient_31_3_pos
  · exact slopeInterior8TensorCoefficient_31_4_pos
  · exact slopeInterior8TensorCoefficient_31_5_pos
  · exact slopeInterior8TensorCoefficient_31_6_pos
  · exact slopeInterior8TensorCoefficient_31_7_pos
  · exact slopeInterior8TensorCoefficient_31_8_pos
  · exact slopeInterior8TensorCoefficient_31_9_pos

theorem slopeInterior8TensorCoefficient_row32_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 32 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_32_0_pos
  · exact slopeInterior8TensorCoefficient_32_1_pos
  · exact slopeInterior8TensorCoefficient_32_2_pos
  · exact slopeInterior8TensorCoefficient_32_3_pos
  · exact slopeInterior8TensorCoefficient_32_4_pos
  · exact slopeInterior8TensorCoefficient_32_5_pos
  · exact slopeInterior8TensorCoefficient_32_6_pos
  · exact slopeInterior8TensorCoefficient_32_7_pos
  · exact slopeInterior8TensorCoefficient_32_8_pos
  · exact slopeInterior8TensorCoefficient_32_9_pos

theorem slopeInterior8TensorCoefficient_row33_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 33 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_33_0_pos
  · exact slopeInterior8TensorCoefficient_33_1_pos
  · exact slopeInterior8TensorCoefficient_33_2_pos
  · exact slopeInterior8TensorCoefficient_33_3_pos
  · exact slopeInterior8TensorCoefficient_33_4_pos
  · exact slopeInterior8TensorCoefficient_33_5_pos
  · exact slopeInterior8TensorCoefficient_33_6_pos
  · exact slopeInterior8TensorCoefficient_33_7_pos
  · exact slopeInterior8TensorCoefficient_33_8_pos
  · exact slopeInterior8TensorCoefficient_33_9_pos

theorem slopeInterior8TensorCoefficient_row34_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 34 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_34_0_pos
  · exact slopeInterior8TensorCoefficient_34_1_pos
  · exact slopeInterior8TensorCoefficient_34_2_pos
  · exact slopeInterior8TensorCoefficient_34_3_pos
  · exact slopeInterior8TensorCoefficient_34_4_pos
  · exact slopeInterior8TensorCoefficient_34_5_pos
  · exact slopeInterior8TensorCoefficient_34_6_pos
  · exact slopeInterior8TensorCoefficient_34_7_pos
  · exact slopeInterior8TensorCoefficient_34_8_pos
  · exact slopeInterior8TensorCoefficient_34_9_pos

theorem slopeInterior8TensorCoefficient_row35_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 35 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_35_0_pos
  · exact slopeInterior8TensorCoefficient_35_1_pos
  · exact slopeInterior8TensorCoefficient_35_2_pos
  · exact slopeInterior8TensorCoefficient_35_3_pos
  · exact slopeInterior8TensorCoefficient_35_4_pos
  · exact slopeInterior8TensorCoefficient_35_5_pos
  · exact slopeInterior8TensorCoefficient_35_6_pos
  · exact slopeInterior8TensorCoefficient_35_7_pos
  · exact slopeInterior8TensorCoefficient_35_8_pos
  · exact slopeInterior8TensorCoefficient_35_9_pos

theorem slopeInterior8TensorCoefficient_row36_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 36 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_36_0_pos
  · exact slopeInterior8TensorCoefficient_36_1_pos
  · exact slopeInterior8TensorCoefficient_36_2_pos
  · exact slopeInterior8TensorCoefficient_36_3_pos
  · exact slopeInterior8TensorCoefficient_36_4_pos
  · exact slopeInterior8TensorCoefficient_36_5_pos
  · exact slopeInterior8TensorCoefficient_36_6_pos
  · exact slopeInterior8TensorCoefficient_36_7_pos
  · exact slopeInterior8TensorCoefficient_36_8_pos
  · exact slopeInterior8TensorCoefficient_36_9_pos

theorem slopeInterior8TensorCoefficient_row37_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 37 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_37_0_pos
  · exact slopeInterior8TensorCoefficient_37_1_pos
  · exact slopeInterior8TensorCoefficient_37_2_pos
  · exact slopeInterior8TensorCoefficient_37_3_pos
  · exact slopeInterior8TensorCoefficient_37_4_pos
  · exact slopeInterior8TensorCoefficient_37_5_pos
  · exact slopeInterior8TensorCoefficient_37_6_pos
  · exact slopeInterior8TensorCoefficient_37_7_pos
  · exact slopeInterior8TensorCoefficient_37_8_pos
  · exact slopeInterior8TensorCoefficient_37_9_pos

theorem slopeInterior8TensorCoefficient_row38_pos (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient 38 B := by
  fin_cases B
  · exact slopeInterior8TensorCoefficient_38_0_pos
  · exact slopeInterior8TensorCoefficient_38_1_pos
  · exact slopeInterior8TensorCoefficient_38_2_pos
  · exact slopeInterior8TensorCoefficient_38_3_pos
  · exact slopeInterior8TensorCoefficient_38_4_pos
  · exact slopeInterior8TensorCoefficient_38_5_pos
  · exact slopeInterior8TensorCoefficient_38_6_pos
  · exact slopeInterior8TensorCoefficient_38_7_pos
  · exact slopeInterior8TensorCoefficient_38_8_pos
  · exact slopeInterior8TensorCoefficient_38_9_pos

theorem slopeInterior8TensorCoefficient_pos (A : Fin 39) (B : Fin 10) :
    0 < slopeInterior8TensorCoefficient A B := by
  fin_cases A
  · exact slopeInterior8TensorCoefficient_row0_pos B
  · exact slopeInterior8TensorCoefficient_row1_pos B
  · exact slopeInterior8TensorCoefficient_row2_pos B
  · exact slopeInterior8TensorCoefficient_row3_pos B
  · exact slopeInterior8TensorCoefficient_row4_pos B
  · exact slopeInterior8TensorCoefficient_row5_pos B
  · exact slopeInterior8TensorCoefficient_row6_pos B
  · exact slopeInterior8TensorCoefficient_row7_pos B
  · exact slopeInterior8TensorCoefficient_row8_pos B
  · exact slopeInterior8TensorCoefficient_row9_pos B
  · exact slopeInterior8TensorCoefficient_row10_pos B
  · exact slopeInterior8TensorCoefficient_row11_pos B
  · exact slopeInterior8TensorCoefficient_row12_pos B
  · exact slopeInterior8TensorCoefficient_row13_pos B
  · exact slopeInterior8TensorCoefficient_row14_pos B
  · exact slopeInterior8TensorCoefficient_row15_pos B
  · exact slopeInterior8TensorCoefficient_row16_pos B
  · exact slopeInterior8TensorCoefficient_row17_pos B
  · exact slopeInterior8TensorCoefficient_row18_pos B
  · exact slopeInterior8TensorCoefficient_row19_pos B
  · exact slopeInterior8TensorCoefficient_row20_pos B
  · exact slopeInterior8TensorCoefficient_row21_pos B
  · exact slopeInterior8TensorCoefficient_row22_pos B
  · exact slopeInterior8TensorCoefficient_row23_pos B
  · exact slopeInterior8TensorCoefficient_row24_pos B
  · exact slopeInterior8TensorCoefficient_row25_pos B
  · exact slopeInterior8TensorCoefficient_row26_pos B
  · exact slopeInterior8TensorCoefficient_row27_pos B
  · exact slopeInterior8TensorCoefficient_row28_pos B
  · exact slopeInterior8TensorCoefficient_row29_pos B
  · exact slopeInterior8TensorCoefficient_row30_pos B
  · exact slopeInterior8TensorCoefficient_row31_pos B
  · exact slopeInterior8TensorCoefficient_row32_pos B
  · exact slopeInterior8TensorCoefficient_row33_pos B
  · exact slopeInterior8TensorCoefficient_row34_pos B
  · exact slopeInterior8TensorCoefficient_row35_pos B
  · exact slopeInterior8TensorCoefficient_row36_pos B
  · exact slopeInterior8TensorCoefficient_row37_pos B
  · exact slopeInterior8TensorCoefficient_row38_pos B

theorem slopeInterior8Quotient_unit_pos (t v : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < slopeInterior8Quotient ((4/5)*t) ((361/25)*v) := by
  rw [←slopeInterior8TensorValue_reconstruction]
  apply kineticBernstein_pos 38 _ t _ ht0 ht1
  intro A hA
  apply kineticBernstein_pos 9 _ v _ hv0 hv1
  intro B hB
  exact slopeInterior8TensorCoefficient_pos ⟨A,hA⟩ ⟨B,hB⟩

theorem slopeInterior8Quotient_pos (h r : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 4/5) (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    0 < slopeInterior8Quotient h r := by
  have ht0 : 0 ≤ h/(4/5:ℝ) := div_nonneg hh0 (by norm_num)
  have ht1 : h/(4/5:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hh1)
  have hv0 : 0 ≤ r/(361/25:ℝ) := div_nonneg hr0 (by norm_num)
  have hv1 : r/(361/25:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hr1)
  have hp := slopeInterior8Quotient_unit_pos (h/(4/5)) (r/(361/25)) ht0 ht1 hv0 hv1
  have he : (4/5:ℝ)*(h/(4/5))=h := by ring
  have re : (361/25:ℝ)*(r/(361/25))=r := by ring
  simpa only [he,re] using hp

theorem negKineticSlopeControl_interior_8_pos (h r : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 4/5) (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    0 < negKineticSlopeControl h (9-r*h^2) (1/3) 8 := by
  rw [slopeInterior8_factor]
  exact mul_pos (pow_pos hh0 4) (slopeInterior8Quotient_pos h r hh0.le hh1 hr0 hr1)

end
end HTGeometry.ThetaRatioKineticContraction

