import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Row1Norms

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullCoefficient77Row1Norm (B : ℕ) : {c : ℝ // boundaryFullCoefficient77 1 B=c} := by

  have he : boundaryFullCoefficient77 1 B=boundaryFullCoefficient77 1 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryFullCoefficient77]

    rw [(boundaryLowCoefficient77Row1Norm B).property,
      (boundaryReCoefficient77_0Row1Norm B).property,
      (boundaryReCoefficient77_1Row1Norm B).property,
      (boundaryReCoefficient77_2Row1Norm B).property,
      (boundaryReCoefficient77_3Row1Norm B).property,
      (boundaryReCoefficient77_4Row1Norm B).property,
      (boundaryReCoefficient77_5Row1Norm B).property,
      (boundaryReCoefficient77_6Row1Norm B).property,
      (boundaryReCoefficient77_7Row1Norm B).property,
      (boundaryReCoefficient77_8Row1Norm B).property,
      (boundaryReCoefficient77_9Row1Norm B).property,
      (boundaryReCoefficient77_10Row1Norm B).property,
      (boundaryReCoefficient77_11Row1Norm B).property,
      (boundaryReCoefficient77_12Row1Norm B).property,
      (boundaryReCoefficient77_13Row1Norm B).property,
      (boundaryReCoefficient77_14Row1Norm B).property,
      (boundaryReCoefficient77_15Row1Norm B).property,
      (boundaryReCoefficient77_16Row1Norm B).property,
      (boundaryReCoefficient77_17Row1Norm B).property,
      (boundaryReCoefficient77_18Row1Norm B).property,
      (boundaryReCoefficient77_19Row1Norm B).property,
      (boundaryReCoefficient77_20Row1Norm B).property,
      (boundaryReCoefficient77_21Row1Norm B).property,
      (boundaryReCoefficient77_22Row1Norm B).property,
      (boundaryImCoefficient77_0Row1Norm B).property,
      (boundaryImCoefficient77_1Row1Norm B).property,
      (boundaryImCoefficient77_2Row1Norm B).property,
      (boundaryImCoefficient77_3Row1Norm B).property,
      (boundaryImCoefficient77_4Row1Norm B).property,
      (boundaryImCoefficient77_5Row1Norm B).property,
      (boundaryImCoefficient77_6Row1Norm B).property,
      (boundaryImCoefficient77_7Row1Norm B).property,
      (boundaryImCoefficient77_8Row1Norm B).property,
      (boundaryImCoefficient77_9Row1Norm B).property,
      (boundaryImCoefficient77_10Row1Norm B).property,
      (boundaryImCoefficient77_11Row1Norm B).property,
      (boundaryImCoefficient77_12Row1Norm B).property,
      (boundaryImCoefficient77_13Row1Norm B).property,
      (boundaryImCoefficient77_14Row1Norm B).property,
      (boundaryImCoefficient77_15Row1Norm B).property,
      (boundaryImCoefficient77_16Row1Norm B).property,
      (boundaryImCoefficient77_17Row1Norm B).property,
      (boundaryImCoefficient77_18Row1Norm B).property,
      (boundaryImCoefficient77_19Row1Norm B).property,
      (boundaryImCoefficient77_20Row1Norm B).property,
      (boundaryImCoefficient77_21Row1Norm B).property]

    dsimp only [boundaryLowCoefficient77Row1Norm,boundaryReCoefficient77_0Row1Norm,boundaryReCoefficient77_1Row1Norm,boundaryReCoefficient77_2Row1Norm,boundaryReCoefficient77_3Row1Norm,boundaryReCoefficient77_4Row1Norm,boundaryReCoefficient77_5Row1Norm,boundaryReCoefficient77_6Row1Norm,boundaryReCoefficient77_7Row1Norm,boundaryReCoefficient77_8Row1Norm,boundaryReCoefficient77_9Row1Norm,boundaryReCoefficient77_10Row1Norm,boundaryReCoefficient77_11Row1Norm,boundaryReCoefficient77_12Row1Norm,boundaryReCoefficient77_13Row1Norm,boundaryReCoefficient77_14Row1Norm,boundaryReCoefficient77_15Row1Norm,boundaryReCoefficient77_16Row1Norm,boundaryReCoefficient77_17Row1Norm,boundaryReCoefficient77_18Row1Norm,boundaryReCoefficient77_19Row1Norm,boundaryReCoefficient77_20Row1Norm,boundaryReCoefficient77_21Row1Norm,boundaryReCoefficient77_22Row1Norm,boundaryImCoefficient77_0Row1Norm,boundaryImCoefficient77_1Row1Norm,boundaryImCoefficient77_2Row1Norm,boundaryImCoefficient77_3Row1Norm,boundaryImCoefficient77_4Row1Norm,boundaryImCoefficient77_5Row1Norm,boundaryImCoefficient77_6Row1Norm,boundaryImCoefficient77_7Row1Norm,boundaryImCoefficient77_8Row1Norm,boundaryImCoefficient77_9Row1Norm,boundaryImCoefficient77_10Row1Norm,boundaryImCoefficient77_11Row1Norm,boundaryImCoefficient77_12Row1Norm,boundaryImCoefficient77_13Row1Norm,boundaryImCoefficient77_14Row1Norm,boundaryImCoefficient77_15Row1Norm,boundaryImCoefficient77_16Row1Norm,boundaryImCoefficient77_17Row1Norm,boundaryImCoefficient77_18Row1Norm,boundaryImCoefficient77_19Row1Norm,boundaryImCoefficient77_20Row1Norm,boundaryImCoefficient77_21Row1Norm]

    ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


theorem boundaryFullCoefficient77_1_0_pos : 0<boundaryFullCoefficient77 1 0 := by

  rw [(boundaryFullCoefficient77Row1Norm 0).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_1_pos : 0<boundaryFullCoefficient77 1 1 := by

  rw [(boundaryFullCoefficient77Row1Norm 1).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_2_pos : 0<boundaryFullCoefficient77 1 2 := by

  rw [(boundaryFullCoefficient77Row1Norm 2).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_3_pos : 0<boundaryFullCoefficient77 1 3 := by

  rw [(boundaryFullCoefficient77Row1Norm 3).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_4_pos : 0<boundaryFullCoefficient77 1 4 := by

  rw [(boundaryFullCoefficient77Row1Norm 4).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_5_pos : 0<boundaryFullCoefficient77 1 5 := by

  rw [(boundaryFullCoefficient77Row1Norm 5).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_6_pos : 0<boundaryFullCoefficient77 1 6 := by

  rw [(boundaryFullCoefficient77Row1Norm 6).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_7_pos : 0<boundaryFullCoefficient77 1 7 := by

  rw [(boundaryFullCoefficient77Row1Norm 7).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_8_pos : 0<boundaryFullCoefficient77 1 8 := by

  rw [(boundaryFullCoefficient77Row1Norm 8).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_9_pos : 0<boundaryFullCoefficient77 1 9 := by

  rw [(boundaryFullCoefficient77Row1Norm 9).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_10_pos : 0<boundaryFullCoefficient77 1 10 := by

  rw [(boundaryFullCoefficient77Row1Norm 10).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_11_pos : 0<boundaryFullCoefficient77 1 11 := by

  rw [(boundaryFullCoefficient77Row1Norm 11).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_12_pos : 0<boundaryFullCoefficient77 1 12 := by

  rw [(boundaryFullCoefficient77Row1Norm 12).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_13_pos : 0<boundaryFullCoefficient77 1 13 := by

  rw [(boundaryFullCoefficient77Row1Norm 13).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_14_pos : 0<boundaryFullCoefficient77 1 14 := by

  rw [(boundaryFullCoefficient77Row1Norm 14).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_15_pos : 0<boundaryFullCoefficient77 1 15 := by

  rw [(boundaryFullCoefficient77Row1Norm 15).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_16_pos : 0<boundaryFullCoefficient77 1 16 := by

  rw [(boundaryFullCoefficient77Row1Norm 16).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_17_pos : 0<boundaryFullCoefficient77 1 17 := by

  rw [(boundaryFullCoefficient77Row1Norm 17).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_18_pos : 0<boundaryFullCoefficient77 1 18 := by

  rw [(boundaryFullCoefficient77Row1Norm 18).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_19_pos : 0<boundaryFullCoefficient77 1 19 := by

  rw [(boundaryFullCoefficient77Row1Norm 19).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_20_pos : 0<boundaryFullCoefficient77 1 20 := by

  rw [(boundaryFullCoefficient77Row1Norm 20).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_21_pos : 0<boundaryFullCoefficient77 1 21 := by

  rw [(boundaryFullCoefficient77Row1Norm 21).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_22_pos : 0<boundaryFullCoefficient77 1 22 := by

  rw [(boundaryFullCoefficient77Row1Norm 22).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_23_pos : 0<boundaryFullCoefficient77 1 23 := by

  rw [(boundaryFullCoefficient77Row1Norm 23).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_24_pos : 0<boundaryFullCoefficient77 1 24 := by

  rw [(boundaryFullCoefficient77Row1Norm 24).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_25_pos : 0<boundaryFullCoefficient77 1 25 := by

  rw [(boundaryFullCoefficient77Row1Norm 25).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_26_pos : 0<boundaryFullCoefficient77 1 26 := by

  rw [(boundaryFullCoefficient77Row1Norm 26).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_27_pos : 0<boundaryFullCoefficient77 1 27 := by

  rw [(boundaryFullCoefficient77Row1Norm 27).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_28_pos : 0<boundaryFullCoefficient77 1 28 := by

  rw [(boundaryFullCoefficient77Row1Norm 28).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_29_pos : 0<boundaryFullCoefficient77 1 29 := by

  rw [(boundaryFullCoefficient77Row1Norm 29).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_30_pos : 0<boundaryFullCoefficient77 1 30 := by

  rw [(boundaryFullCoefficient77Row1Norm 30).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_31_pos : 0<boundaryFullCoefficient77 1 31 := by

  rw [(boundaryFullCoefficient77Row1Norm 31).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_32_pos : 0<boundaryFullCoefficient77 1 32 := by

  rw [(boundaryFullCoefficient77Row1Norm 32).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_33_pos : 0<boundaryFullCoefficient77 1 33 := by

  rw [(boundaryFullCoefficient77Row1Norm 33).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_34_pos : 0<boundaryFullCoefficient77 1 34 := by

  rw [(boundaryFullCoefficient77Row1Norm 34).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_35_pos : 0<boundaryFullCoefficient77 1 35 := by

  rw [(boundaryFullCoefficient77Row1Norm 35).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_1_36_pos : 0<boundaryFullCoefficient77 1 36 := by

  rw [(boundaryFullCoefficient77Row1Norm 36).property]

  norm_num [boundaryFullCoefficient77Row1Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


end

end HTGeometry.ThetaRatioInfinity
