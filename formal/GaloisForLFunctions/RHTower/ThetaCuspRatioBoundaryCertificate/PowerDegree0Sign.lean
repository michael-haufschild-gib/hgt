import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.PowerDegree0Norm

import Mathlib.Tactic.FinCases

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

theorem boundaryFullCoefficientForm77_clock_zero (x : ℕ → ℝ) :
    boundaryFullCoefficientForm77 0 x=
      boundaryFullPowerRow77 0 (fun q => boundaryS77^q*x q) := by
  rw [boundaryFullCoefficientForm77_power_rows,Finset.sum_eq_single 0]
  · simp [degreeElevationCoefficient]
  · intro e he hne
    have hn : ¬e≤0 := by omega
    simp only [degreeElevationCoefficient,hn,if_false,mul_zero,zero_mul]
  · norm_num

theorem boundaryFullCoefficient77_0_0_pos : 0<boundaryFullCoefficient77 0 0 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_1_pos : 0<boundaryFullCoefficient77 0 1 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_2_pos : 0<boundaryFullCoefficient77 0 2 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_3_pos : 0<boundaryFullCoefficient77 0 3 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_4_pos : 0<boundaryFullCoefficient77 0 4 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_5_pos : 0<boundaryFullCoefficient77 0 5 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_6_pos : 0<boundaryFullCoefficient77 0 6 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_7_pos : 0<boundaryFullCoefficient77 0 7 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_8_pos : 0<boundaryFullCoefficient77 0 8 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_9_pos : 0<boundaryFullCoefficient77 0 9 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_10_pos : 0<boundaryFullCoefficient77 0 10 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_11_pos : 0<boundaryFullCoefficient77 0 11 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_12_pos : 0<boundaryFullCoefficient77 0 12 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_13_pos : 0<boundaryFullCoefficient77 0 13 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_14_pos : 0<boundaryFullCoefficient77 0 14 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_15_pos : 0<boundaryFullCoefficient77 0 15 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_16_pos : 0<boundaryFullCoefficient77 0 16 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_17_pos : 0<boundaryFullCoefficient77 0 17 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_18_pos : 0<boundaryFullCoefficient77 0 18 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_19_pos : 0<boundaryFullCoefficient77 0 19 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_20_pos : 0<boundaryFullCoefficient77 0 20 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_21_pos : 0<boundaryFullCoefficient77 0 21 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_22_pos : 0<boundaryFullCoefficient77 0 22 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_23_pos : 0<boundaryFullCoefficient77 0 23 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_24_pos : 0<boundaryFullCoefficient77 0 24 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_25_pos : 0<boundaryFullCoefficient77 0 25 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_26_pos : 0<boundaryFullCoefficient77 0 26 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_27_pos : 0<boundaryFullCoefficient77 0 27 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_28_pos : 0<boundaryFullCoefficient77 0 28 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_29_pos : 0<boundaryFullCoefficient77 0 29 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_30_pos : 0<boundaryFullCoefficient77 0 30 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_31_pos : 0<boundaryFullCoefficient77 0 31 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_32_pos : 0<boundaryFullCoefficient77 0 32 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_33_pos : 0<boundaryFullCoefficient77 0 33 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_34_pos : 0<boundaryFullCoefficient77 0 34 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_35_pos : 0<boundaryFullCoefficient77 0 35 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_0_36_pos : 0<boundaryFullCoefficient77 0 36 := by

  rw [← boundaryFullCoefficientForm77_evaluate,boundaryFullCoefficientForm77_clock_zero,

    (boundaryFullPowerRow77Degree0Norm _).property]

  norm_num [boundaryFullPowerRow77Degree0Norm,boundaryS77,degreeElevationCoefficient,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem boundaryFullCoefficient77_row0_pos (B : Fin 37) : 0<boundaryFullCoefficient77 0 B := by

  fin_cases B

  · exact boundaryFullCoefficient77_0_0_pos

  · exact boundaryFullCoefficient77_0_1_pos

  · exact boundaryFullCoefficient77_0_2_pos

  · exact boundaryFullCoefficient77_0_3_pos

  · exact boundaryFullCoefficient77_0_4_pos

  · exact boundaryFullCoefficient77_0_5_pos

  · exact boundaryFullCoefficient77_0_6_pos

  · exact boundaryFullCoefficient77_0_7_pos

  · exact boundaryFullCoefficient77_0_8_pos

  · exact boundaryFullCoefficient77_0_9_pos

  · exact boundaryFullCoefficient77_0_10_pos

  · exact boundaryFullCoefficient77_0_11_pos

  · exact boundaryFullCoefficient77_0_12_pos

  · exact boundaryFullCoefficient77_0_13_pos

  · exact boundaryFullCoefficient77_0_14_pos

  · exact boundaryFullCoefficient77_0_15_pos

  · exact boundaryFullCoefficient77_0_16_pos

  · exact boundaryFullCoefficient77_0_17_pos

  · exact boundaryFullCoefficient77_0_18_pos

  · exact boundaryFullCoefficient77_0_19_pos

  · exact boundaryFullCoefficient77_0_20_pos

  · exact boundaryFullCoefficient77_0_21_pos

  · exact boundaryFullCoefficient77_0_22_pos

  · exact boundaryFullCoefficient77_0_23_pos

  · exact boundaryFullCoefficient77_0_24_pos

  · exact boundaryFullCoefficient77_0_25_pos

  · exact boundaryFullCoefficient77_0_26_pos

  · exact boundaryFullCoefficient77_0_27_pos

  · exact boundaryFullCoefficient77_0_28_pos

  · exact boundaryFullCoefficient77_0_29_pos

  · exact boundaryFullCoefficient77_0_30_pos

  · exact boundaryFullCoefficient77_0_31_pos

  · exact boundaryFullCoefficient77_0_32_pos

  · exact boundaryFullCoefficient77_0_33_pos

  · exact boundaryFullCoefficient77_0_34_pos

  · exact boundaryFullCoefficient77_0_35_pos

  · exact boundaryFullCoefficient77_0_36_pos



end

end HTGeometry.ThetaRatioInfinity
