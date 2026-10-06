import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.FormRow5Norms

import Mathlib.Tactic.FinCases

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullCoefficientForm77Row5Norm (x : ℕ → ℝ) : {c : ℝ // boundaryFullCoefficientForm77 5 x=c} := by

  have he : boundaryFullCoefficientForm77 5 x=boundaryFullCoefficientForm77 5 x := rfl

  conv at he =>

    rhs

    dsimp only [boundaryFullCoefficientForm77]

    rw [(boundaryReCoefficientForm77_0Row5Norm x).property,
      (boundaryReCoefficientForm77_1Row5Norm x).property,
      (boundaryReCoefficientForm77_2Row5Norm x).property,
      (boundaryReCoefficientForm77_3Row5Norm x).property,
      (boundaryReCoefficientForm77_4Row5Norm x).property,
      (boundaryReCoefficientForm77_5Row5Norm x).property,
      (boundaryReCoefficientForm77_6Row5Norm x).property,
      (boundaryReCoefficientForm77_7Row5Norm x).property,
      (boundaryReCoefficientForm77_8Row5Norm x).property,
      (boundaryReCoefficientForm77_9Row5Norm x).property,
      (boundaryReCoefficientForm77_10Row5Norm x).property,
      (boundaryReCoefficientForm77_11Row5Norm x).property,
      (boundaryReCoefficientForm77_12Row5Norm x).property,
      (boundaryReCoefficientForm77_13Row5Norm x).property,
      (boundaryReCoefficientForm77_14Row5Norm x).property,
      (boundaryReCoefficientForm77_15Row5Norm x).property,
      (boundaryReCoefficientForm77_16Row5Norm x).property,
      (boundaryReCoefficientForm77_17Row5Norm x).property,
      (boundaryReCoefficientForm77_18Row5Norm x).property,
      (boundaryReCoefficientForm77_19Row5Norm x).property,
      (boundaryReCoefficientForm77_20Row5Norm x).property,
      (boundaryReCoefficientForm77_21Row5Norm x).property,
      (boundaryReCoefficientForm77_22Row5Norm x).property,
      (boundaryImCoefficientForm77_0Row5Norm x).property,
      (boundaryImCoefficientForm77_1Row5Norm x).property,
      (boundaryImCoefficientForm77_2Row5Norm x).property,
      (boundaryImCoefficientForm77_3Row5Norm x).property,
      (boundaryImCoefficientForm77_4Row5Norm x).property,
      (boundaryImCoefficientForm77_5Row5Norm x).property,
      (boundaryImCoefficientForm77_6Row5Norm x).property,
      (boundaryImCoefficientForm77_7Row5Norm x).property,
      (boundaryImCoefficientForm77_8Row5Norm x).property,
      (boundaryImCoefficientForm77_9Row5Norm x).property,
      (boundaryImCoefficientForm77_10Row5Norm x).property,
      (boundaryImCoefficientForm77_11Row5Norm x).property,
      (boundaryImCoefficientForm77_12Row5Norm x).property,
      (boundaryImCoefficientForm77_13Row5Norm x).property,
      (boundaryImCoefficientForm77_14Row5Norm x).property,
      (boundaryImCoefficientForm77_15Row5Norm x).property,
      (boundaryImCoefficientForm77_16Row5Norm x).property,
      (boundaryImCoefficientForm77_17Row5Norm x).property,
      (boundaryImCoefficientForm77_18Row5Norm x).property,
      (boundaryImCoefficientForm77_19Row5Norm x).property,
      (boundaryImCoefficientForm77_20Row5Norm x).property,
      (boundaryImCoefficientForm77_21Row5Norm x).property,
      (boundaryLowCoefficientForm77Row5Norm x).property]

    dsimp only [boundaryReCoefficientForm77_0Row5Norm,boundaryReCoefficientForm77_1Row5Norm,boundaryReCoefficientForm77_2Row5Norm,boundaryReCoefficientForm77_3Row5Norm,boundaryReCoefficientForm77_4Row5Norm,boundaryReCoefficientForm77_5Row5Norm,boundaryReCoefficientForm77_6Row5Norm,boundaryReCoefficientForm77_7Row5Norm,boundaryReCoefficientForm77_8Row5Norm,boundaryReCoefficientForm77_9Row5Norm,boundaryReCoefficientForm77_10Row5Norm,boundaryReCoefficientForm77_11Row5Norm,boundaryReCoefficientForm77_12Row5Norm,boundaryReCoefficientForm77_13Row5Norm,boundaryReCoefficientForm77_14Row5Norm,boundaryReCoefficientForm77_15Row5Norm,boundaryReCoefficientForm77_16Row5Norm,boundaryReCoefficientForm77_17Row5Norm,boundaryReCoefficientForm77_18Row5Norm,boundaryReCoefficientForm77_19Row5Norm,boundaryReCoefficientForm77_20Row5Norm,boundaryReCoefficientForm77_21Row5Norm,boundaryReCoefficientForm77_22Row5Norm,boundaryImCoefficientForm77_0Row5Norm,boundaryImCoefficientForm77_1Row5Norm,boundaryImCoefficientForm77_2Row5Norm,boundaryImCoefficientForm77_3Row5Norm,boundaryImCoefficientForm77_4Row5Norm,boundaryImCoefficientForm77_5Row5Norm,boundaryImCoefficientForm77_6Row5Norm,boundaryImCoefficientForm77_7Row5Norm,boundaryImCoefficientForm77_8Row5Norm,boundaryImCoefficientForm77_9Row5Norm,boundaryImCoefficientForm77_10Row5Norm,boundaryImCoefficientForm77_11Row5Norm,boundaryImCoefficientForm77_12Row5Norm,boundaryImCoefficientForm77_13Row5Norm,boundaryImCoefficientForm77_14Row5Norm,boundaryImCoefficientForm77_15Row5Norm,boundaryImCoefficientForm77_16Row5Norm,boundaryImCoefficientForm77_17Row5Norm,boundaryImCoefficientForm77_18Row5Norm,boundaryImCoefficientForm77_19Row5Norm,boundaryImCoefficientForm77_20Row5Norm,boundaryImCoefficientForm77_21Row5Norm,boundaryLowCoefficientForm77Row5Norm]

    ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


theorem boundaryFullCoefficient77_5_0_pos : 0<boundaryFullCoefficient77 5 0 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 0)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_1_pos : 0<boundaryFullCoefficient77 5 1 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 1)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_2_pos : 0<boundaryFullCoefficient77 5 2 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 2)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_3_pos : 0<boundaryFullCoefficient77 5 3 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 3)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_4_pos : 0<boundaryFullCoefficient77 5 4 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 4)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_5_pos : 0<boundaryFullCoefficient77 5 5 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 5)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_6_pos : 0<boundaryFullCoefficient77 5 6 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 6)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_7_pos : 0<boundaryFullCoefficient77 5 7 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 7)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_8_pos : 0<boundaryFullCoefficient77 5 8 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 8)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_9_pos : 0<boundaryFullCoefficient77 5 9 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 9)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_10_pos : 0<boundaryFullCoefficient77 5 10 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 10)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_11_pos : 0<boundaryFullCoefficient77 5 11 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 11)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_12_pos : 0<boundaryFullCoefficient77 5 12 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 12)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_13_pos : 0<boundaryFullCoefficient77 5 13 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 13)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_14_pos : 0<boundaryFullCoefficient77 5 14 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 14)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_15_pos : 0<boundaryFullCoefficient77 5 15 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 15)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_16_pos : 0<boundaryFullCoefficient77 5 16 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 16)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_17_pos : 0<boundaryFullCoefficient77 5 17 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 17)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_18_pos : 0<boundaryFullCoefficient77 5 18 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 18)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_19_pos : 0<boundaryFullCoefficient77 5 19 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 19)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_20_pos : 0<boundaryFullCoefficient77 5 20 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 20)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_21_pos : 0<boundaryFullCoefficient77 5 21 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 21)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_22_pos : 0<boundaryFullCoefficient77 5 22 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 22)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_23_pos : 0<boundaryFullCoefficient77 5 23 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 23)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_24_pos : 0<boundaryFullCoefficient77 5 24 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 24)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_25_pos : 0<boundaryFullCoefficient77 5 25 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 25)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_26_pos : 0<boundaryFullCoefficient77 5 26 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 26)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_27_pos : 0<boundaryFullCoefficient77 5 27 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 27)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_28_pos : 0<boundaryFullCoefficient77 5 28 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 28)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_29_pos : 0<boundaryFullCoefficient77 5 29 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 29)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_30_pos : 0<boundaryFullCoefficient77 5 30 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 30)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_31_pos : 0<boundaryFullCoefficient77 5 31 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 31)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_32_pos : 0<boundaryFullCoefficient77 5 32 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 32)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_33_pos : 0<boundaryFullCoefficient77 5 33 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 33)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_34_pos : 0<boundaryFullCoefficient77 5 34 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 34)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_35_pos : 0<boundaryFullCoefficient77 5 35 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 35)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_5_36_pos : 0<boundaryFullCoefficient77 5 36 := by

  rw [← boundaryFullCoefficientForm77_evaluate,(boundaryFullCoefficientForm77Row5Norm (fun q => degreeElevationCoefficient 36 q 36)).property]

  norm_num [boundaryFullCoefficientForm77Row5Norm,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_row5_pos (B : Fin 37) : 0<boundaryFullCoefficient77 5 B := by

  fin_cases B

  · exact boundaryFullCoefficient77_5_0_pos

  · exact boundaryFullCoefficient77_5_1_pos

  · exact boundaryFullCoefficient77_5_2_pos

  · exact boundaryFullCoefficient77_5_3_pos

  · exact boundaryFullCoefficient77_5_4_pos

  · exact boundaryFullCoefficient77_5_5_pos

  · exact boundaryFullCoefficient77_5_6_pos

  · exact boundaryFullCoefficient77_5_7_pos

  · exact boundaryFullCoefficient77_5_8_pos

  · exact boundaryFullCoefficient77_5_9_pos

  · exact boundaryFullCoefficient77_5_10_pos

  · exact boundaryFullCoefficient77_5_11_pos

  · exact boundaryFullCoefficient77_5_12_pos

  · exact boundaryFullCoefficient77_5_13_pos

  · exact boundaryFullCoefficient77_5_14_pos

  · exact boundaryFullCoefficient77_5_15_pos

  · exact boundaryFullCoefficient77_5_16_pos

  · exact boundaryFullCoefficient77_5_17_pos

  · exact boundaryFullCoefficient77_5_18_pos

  · exact boundaryFullCoefficient77_5_19_pos

  · exact boundaryFullCoefficient77_5_20_pos

  · exact boundaryFullCoefficient77_5_21_pos

  · exact boundaryFullCoefficient77_5_22_pos

  · exact boundaryFullCoefficient77_5_23_pos

  · exact boundaryFullCoefficient77_5_24_pos

  · exact boundaryFullCoefficient77_5_25_pos

  · exact boundaryFullCoefficient77_5_26_pos

  · exact boundaryFullCoefficient77_5_27_pos

  · exact boundaryFullCoefficient77_5_28_pos

  · exact boundaryFullCoefficient77_5_29_pos

  · exact boundaryFullCoefficient77_5_30_pos

  · exact boundaryFullCoefficient77_5_31_pos

  · exact boundaryFullCoefficient77_5_32_pos

  · exact boundaryFullCoefficient77_5_33_pos

  · exact boundaryFullCoefficient77_5_34_pos

  · exact boundaryFullCoefficient77_5_35_pos

  · exact boundaryFullCoefficient77_5_36_pos


end

end HTGeometry.ThetaRatioInfinity
