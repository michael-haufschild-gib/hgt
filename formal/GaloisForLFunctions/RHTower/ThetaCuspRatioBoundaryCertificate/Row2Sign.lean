import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Row2Norms

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullCoefficient77Row2Norm (B : ℕ) : {c : ℝ // boundaryFullCoefficient77 2 B=c} := by

  have he : boundaryFullCoefficient77 2 B=boundaryFullCoefficient77 2 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryFullCoefficient77]

    rw [(boundaryLowCoefficient77Row2Norm B).property,
      (boundaryReCoefficient77_0Row2Norm B).property,
      (boundaryReCoefficient77_1Row2Norm B).property,
      (boundaryReCoefficient77_2Row2Norm B).property,
      (boundaryReCoefficient77_3Row2Norm B).property,
      (boundaryReCoefficient77_4Row2Norm B).property,
      (boundaryReCoefficient77_5Row2Norm B).property,
      (boundaryReCoefficient77_6Row2Norm B).property,
      (boundaryReCoefficient77_7Row2Norm B).property,
      (boundaryReCoefficient77_8Row2Norm B).property,
      (boundaryReCoefficient77_9Row2Norm B).property,
      (boundaryReCoefficient77_10Row2Norm B).property,
      (boundaryReCoefficient77_11Row2Norm B).property,
      (boundaryReCoefficient77_12Row2Norm B).property,
      (boundaryReCoefficient77_13Row2Norm B).property,
      (boundaryReCoefficient77_14Row2Norm B).property,
      (boundaryReCoefficient77_15Row2Norm B).property,
      (boundaryReCoefficient77_16Row2Norm B).property,
      (boundaryReCoefficient77_17Row2Norm B).property,
      (boundaryReCoefficient77_18Row2Norm B).property,
      (boundaryReCoefficient77_19Row2Norm B).property,
      (boundaryReCoefficient77_20Row2Norm B).property,
      (boundaryReCoefficient77_21Row2Norm B).property,
      (boundaryReCoefficient77_22Row2Norm B).property,
      (boundaryImCoefficient77_0Row2Norm B).property,
      (boundaryImCoefficient77_1Row2Norm B).property,
      (boundaryImCoefficient77_2Row2Norm B).property,
      (boundaryImCoefficient77_3Row2Norm B).property,
      (boundaryImCoefficient77_4Row2Norm B).property,
      (boundaryImCoefficient77_5Row2Norm B).property,
      (boundaryImCoefficient77_6Row2Norm B).property,
      (boundaryImCoefficient77_7Row2Norm B).property,
      (boundaryImCoefficient77_8Row2Norm B).property,
      (boundaryImCoefficient77_9Row2Norm B).property,
      (boundaryImCoefficient77_10Row2Norm B).property,
      (boundaryImCoefficient77_11Row2Norm B).property,
      (boundaryImCoefficient77_12Row2Norm B).property,
      (boundaryImCoefficient77_13Row2Norm B).property,
      (boundaryImCoefficient77_14Row2Norm B).property,
      (boundaryImCoefficient77_15Row2Norm B).property,
      (boundaryImCoefficient77_16Row2Norm B).property,
      (boundaryImCoefficient77_17Row2Norm B).property,
      (boundaryImCoefficient77_18Row2Norm B).property,
      (boundaryImCoefficient77_19Row2Norm B).property,
      (boundaryImCoefficient77_20Row2Norm B).property,
      (boundaryImCoefficient77_21Row2Norm B).property]

    dsimp only [boundaryLowCoefficient77Row2Norm,boundaryReCoefficient77_0Row2Norm,boundaryReCoefficient77_1Row2Norm,boundaryReCoefficient77_2Row2Norm,boundaryReCoefficient77_3Row2Norm,boundaryReCoefficient77_4Row2Norm,boundaryReCoefficient77_5Row2Norm,boundaryReCoefficient77_6Row2Norm,boundaryReCoefficient77_7Row2Norm,boundaryReCoefficient77_8Row2Norm,boundaryReCoefficient77_9Row2Norm,boundaryReCoefficient77_10Row2Norm,boundaryReCoefficient77_11Row2Norm,boundaryReCoefficient77_12Row2Norm,boundaryReCoefficient77_13Row2Norm,boundaryReCoefficient77_14Row2Norm,boundaryReCoefficient77_15Row2Norm,boundaryReCoefficient77_16Row2Norm,boundaryReCoefficient77_17Row2Norm,boundaryReCoefficient77_18Row2Norm,boundaryReCoefficient77_19Row2Norm,boundaryReCoefficient77_20Row2Norm,boundaryReCoefficient77_21Row2Norm,boundaryReCoefficient77_22Row2Norm,boundaryImCoefficient77_0Row2Norm,boundaryImCoefficient77_1Row2Norm,boundaryImCoefficient77_2Row2Norm,boundaryImCoefficient77_3Row2Norm,boundaryImCoefficient77_4Row2Norm,boundaryImCoefficient77_5Row2Norm,boundaryImCoefficient77_6Row2Norm,boundaryImCoefficient77_7Row2Norm,boundaryImCoefficient77_8Row2Norm,boundaryImCoefficient77_9Row2Norm,boundaryImCoefficient77_10Row2Norm,boundaryImCoefficient77_11Row2Norm,boundaryImCoefficient77_12Row2Norm,boundaryImCoefficient77_13Row2Norm,boundaryImCoefficient77_14Row2Norm,boundaryImCoefficient77_15Row2Norm,boundaryImCoefficient77_16Row2Norm,boundaryImCoefficient77_17Row2Norm,boundaryImCoefficient77_18Row2Norm,boundaryImCoefficient77_19Row2Norm,boundaryImCoefficient77_20Row2Norm,boundaryImCoefficient77_21Row2Norm]

    ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


theorem boundaryFullCoefficient77_2_0_pos : 0<boundaryFullCoefficient77 2 0 := by

  rw [(boundaryFullCoefficient77Row2Norm 0).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_1_pos : 0<boundaryFullCoefficient77 2 1 := by

  rw [(boundaryFullCoefficient77Row2Norm 1).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_2_pos : 0<boundaryFullCoefficient77 2 2 := by

  rw [(boundaryFullCoefficient77Row2Norm 2).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_3_pos : 0<boundaryFullCoefficient77 2 3 := by

  rw [(boundaryFullCoefficient77Row2Norm 3).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_4_pos : 0<boundaryFullCoefficient77 2 4 := by

  rw [(boundaryFullCoefficient77Row2Norm 4).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_5_pos : 0<boundaryFullCoefficient77 2 5 := by

  rw [(boundaryFullCoefficient77Row2Norm 5).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_6_pos : 0<boundaryFullCoefficient77 2 6 := by

  rw [(boundaryFullCoefficient77Row2Norm 6).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_7_pos : 0<boundaryFullCoefficient77 2 7 := by

  rw [(boundaryFullCoefficient77Row2Norm 7).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_8_pos : 0<boundaryFullCoefficient77 2 8 := by

  rw [(boundaryFullCoefficient77Row2Norm 8).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_9_pos : 0<boundaryFullCoefficient77 2 9 := by

  rw [(boundaryFullCoefficient77Row2Norm 9).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_10_pos : 0<boundaryFullCoefficient77 2 10 := by

  rw [(boundaryFullCoefficient77Row2Norm 10).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_11_pos : 0<boundaryFullCoefficient77 2 11 := by

  rw [(boundaryFullCoefficient77Row2Norm 11).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_12_pos : 0<boundaryFullCoefficient77 2 12 := by

  rw [(boundaryFullCoefficient77Row2Norm 12).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_13_pos : 0<boundaryFullCoefficient77 2 13 := by

  rw [(boundaryFullCoefficient77Row2Norm 13).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_14_pos : 0<boundaryFullCoefficient77 2 14 := by

  rw [(boundaryFullCoefficient77Row2Norm 14).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_15_pos : 0<boundaryFullCoefficient77 2 15 := by

  rw [(boundaryFullCoefficient77Row2Norm 15).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_16_pos : 0<boundaryFullCoefficient77 2 16 := by

  rw [(boundaryFullCoefficient77Row2Norm 16).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_17_pos : 0<boundaryFullCoefficient77 2 17 := by

  rw [(boundaryFullCoefficient77Row2Norm 17).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_18_pos : 0<boundaryFullCoefficient77 2 18 := by

  rw [(boundaryFullCoefficient77Row2Norm 18).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_19_pos : 0<boundaryFullCoefficient77 2 19 := by

  rw [(boundaryFullCoefficient77Row2Norm 19).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_20_pos : 0<boundaryFullCoefficient77 2 20 := by

  rw [(boundaryFullCoefficient77Row2Norm 20).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_21_pos : 0<boundaryFullCoefficient77 2 21 := by

  rw [(boundaryFullCoefficient77Row2Norm 21).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_22_pos : 0<boundaryFullCoefficient77 2 22 := by

  rw [(boundaryFullCoefficient77Row2Norm 22).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_23_pos : 0<boundaryFullCoefficient77 2 23 := by

  rw [(boundaryFullCoefficient77Row2Norm 23).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_24_pos : 0<boundaryFullCoefficient77 2 24 := by

  rw [(boundaryFullCoefficient77Row2Norm 24).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_25_pos : 0<boundaryFullCoefficient77 2 25 := by

  rw [(boundaryFullCoefficient77Row2Norm 25).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_26_pos : 0<boundaryFullCoefficient77 2 26 := by

  rw [(boundaryFullCoefficient77Row2Norm 26).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_27_pos : 0<boundaryFullCoefficient77 2 27 := by

  rw [(boundaryFullCoefficient77Row2Norm 27).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_28_pos : 0<boundaryFullCoefficient77 2 28 := by

  rw [(boundaryFullCoefficient77Row2Norm 28).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_29_pos : 0<boundaryFullCoefficient77 2 29 := by

  rw [(boundaryFullCoefficient77Row2Norm 29).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_30_pos : 0<boundaryFullCoefficient77 2 30 := by

  rw [(boundaryFullCoefficient77Row2Norm 30).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_31_pos : 0<boundaryFullCoefficient77 2 31 := by

  rw [(boundaryFullCoefficient77Row2Norm 31).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_32_pos : 0<boundaryFullCoefficient77 2 32 := by

  rw [(boundaryFullCoefficient77Row2Norm 32).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_33_pos : 0<boundaryFullCoefficient77 2 33 := by

  rw [(boundaryFullCoefficient77Row2Norm 33).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_34_pos : 0<boundaryFullCoefficient77 2 34 := by

  rw [(boundaryFullCoefficient77Row2Norm 34).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_35_pos : 0<boundaryFullCoefficient77 2 35 := by

  rw [(boundaryFullCoefficient77Row2Norm 35).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_2_36_pos : 0<boundaryFullCoefficient77 2 36 := by

  rw [(boundaryFullCoefficient77Row2Norm 36).property]

  norm_num [boundaryFullCoefficient77Row2Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


end

end HTGeometry.ThetaRatioInfinity
