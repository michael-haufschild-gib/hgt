import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Row3Norms

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullCoefficient77Row3Norm (B : ℕ) : {c : ℝ // boundaryFullCoefficient77 3 B=c} := by

  have he : boundaryFullCoefficient77 3 B=boundaryFullCoefficient77 3 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryFullCoefficient77]

    rw [(boundaryLowCoefficient77Row3Norm B).property,
      (boundaryReCoefficient77_0Row3Norm B).property,
      (boundaryReCoefficient77_1Row3Norm B).property,
      (boundaryReCoefficient77_2Row3Norm B).property,
      (boundaryReCoefficient77_3Row3Norm B).property,
      (boundaryReCoefficient77_4Row3Norm B).property,
      (boundaryReCoefficient77_5Row3Norm B).property,
      (boundaryReCoefficient77_6Row3Norm B).property,
      (boundaryReCoefficient77_7Row3Norm B).property,
      (boundaryReCoefficient77_8Row3Norm B).property,
      (boundaryReCoefficient77_9Row3Norm B).property,
      (boundaryReCoefficient77_10Row3Norm B).property,
      (boundaryReCoefficient77_11Row3Norm B).property,
      (boundaryReCoefficient77_12Row3Norm B).property,
      (boundaryReCoefficient77_13Row3Norm B).property,
      (boundaryReCoefficient77_14Row3Norm B).property,
      (boundaryReCoefficient77_15Row3Norm B).property,
      (boundaryReCoefficient77_16Row3Norm B).property,
      (boundaryReCoefficient77_17Row3Norm B).property,
      (boundaryReCoefficient77_18Row3Norm B).property,
      (boundaryReCoefficient77_19Row3Norm B).property,
      (boundaryReCoefficient77_20Row3Norm B).property,
      (boundaryReCoefficient77_21Row3Norm B).property,
      (boundaryReCoefficient77_22Row3Norm B).property,
      (boundaryImCoefficient77_0Row3Norm B).property,
      (boundaryImCoefficient77_1Row3Norm B).property,
      (boundaryImCoefficient77_2Row3Norm B).property,
      (boundaryImCoefficient77_3Row3Norm B).property,
      (boundaryImCoefficient77_4Row3Norm B).property,
      (boundaryImCoefficient77_5Row3Norm B).property,
      (boundaryImCoefficient77_6Row3Norm B).property,
      (boundaryImCoefficient77_7Row3Norm B).property,
      (boundaryImCoefficient77_8Row3Norm B).property,
      (boundaryImCoefficient77_9Row3Norm B).property,
      (boundaryImCoefficient77_10Row3Norm B).property,
      (boundaryImCoefficient77_11Row3Norm B).property,
      (boundaryImCoefficient77_12Row3Norm B).property,
      (boundaryImCoefficient77_13Row3Norm B).property,
      (boundaryImCoefficient77_14Row3Norm B).property,
      (boundaryImCoefficient77_15Row3Norm B).property,
      (boundaryImCoefficient77_16Row3Norm B).property,
      (boundaryImCoefficient77_17Row3Norm B).property,
      (boundaryImCoefficient77_18Row3Norm B).property,
      (boundaryImCoefficient77_19Row3Norm B).property,
      (boundaryImCoefficient77_20Row3Norm B).property,
      (boundaryImCoefficient77_21Row3Norm B).property]

    dsimp only [boundaryLowCoefficient77Row3Norm,boundaryReCoefficient77_0Row3Norm,boundaryReCoefficient77_1Row3Norm,boundaryReCoefficient77_2Row3Norm,boundaryReCoefficient77_3Row3Norm,boundaryReCoefficient77_4Row3Norm,boundaryReCoefficient77_5Row3Norm,boundaryReCoefficient77_6Row3Norm,boundaryReCoefficient77_7Row3Norm,boundaryReCoefficient77_8Row3Norm,boundaryReCoefficient77_9Row3Norm,boundaryReCoefficient77_10Row3Norm,boundaryReCoefficient77_11Row3Norm,boundaryReCoefficient77_12Row3Norm,boundaryReCoefficient77_13Row3Norm,boundaryReCoefficient77_14Row3Norm,boundaryReCoefficient77_15Row3Norm,boundaryReCoefficient77_16Row3Norm,boundaryReCoefficient77_17Row3Norm,boundaryReCoefficient77_18Row3Norm,boundaryReCoefficient77_19Row3Norm,boundaryReCoefficient77_20Row3Norm,boundaryReCoefficient77_21Row3Norm,boundaryReCoefficient77_22Row3Norm,boundaryImCoefficient77_0Row3Norm,boundaryImCoefficient77_1Row3Norm,boundaryImCoefficient77_2Row3Norm,boundaryImCoefficient77_3Row3Norm,boundaryImCoefficient77_4Row3Norm,boundaryImCoefficient77_5Row3Norm,boundaryImCoefficient77_6Row3Norm,boundaryImCoefficient77_7Row3Norm,boundaryImCoefficient77_8Row3Norm,boundaryImCoefficient77_9Row3Norm,boundaryImCoefficient77_10Row3Norm,boundaryImCoefficient77_11Row3Norm,boundaryImCoefficient77_12Row3Norm,boundaryImCoefficient77_13Row3Norm,boundaryImCoefficient77_14Row3Norm,boundaryImCoefficient77_15Row3Norm,boundaryImCoefficient77_16Row3Norm,boundaryImCoefficient77_17Row3Norm,boundaryImCoefficient77_18Row3Norm,boundaryImCoefficient77_19Row3Norm,boundaryImCoefficient77_20Row3Norm,boundaryImCoefficient77_21Row3Norm]

    ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


theorem boundaryFullCoefficient77_3_0_pos : 0<boundaryFullCoefficient77 3 0 := by

  rw [(boundaryFullCoefficient77Row3Norm 0).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_1_pos : 0<boundaryFullCoefficient77 3 1 := by

  rw [(boundaryFullCoefficient77Row3Norm 1).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_2_pos : 0<boundaryFullCoefficient77 3 2 := by

  rw [(boundaryFullCoefficient77Row3Norm 2).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_3_pos : 0<boundaryFullCoefficient77 3 3 := by

  rw [(boundaryFullCoefficient77Row3Norm 3).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_4_pos : 0<boundaryFullCoefficient77 3 4 := by

  rw [(boundaryFullCoefficient77Row3Norm 4).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_5_pos : 0<boundaryFullCoefficient77 3 5 := by

  rw [(boundaryFullCoefficient77Row3Norm 5).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_6_pos : 0<boundaryFullCoefficient77 3 6 := by

  rw [(boundaryFullCoefficient77Row3Norm 6).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_7_pos : 0<boundaryFullCoefficient77 3 7 := by

  rw [(boundaryFullCoefficient77Row3Norm 7).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_8_pos : 0<boundaryFullCoefficient77 3 8 := by

  rw [(boundaryFullCoefficient77Row3Norm 8).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_9_pos : 0<boundaryFullCoefficient77 3 9 := by

  rw [(boundaryFullCoefficient77Row3Norm 9).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_10_pos : 0<boundaryFullCoefficient77 3 10 := by

  rw [(boundaryFullCoefficient77Row3Norm 10).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_11_pos : 0<boundaryFullCoefficient77 3 11 := by

  rw [(boundaryFullCoefficient77Row3Norm 11).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_12_pos : 0<boundaryFullCoefficient77 3 12 := by

  rw [(boundaryFullCoefficient77Row3Norm 12).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_13_pos : 0<boundaryFullCoefficient77 3 13 := by

  rw [(boundaryFullCoefficient77Row3Norm 13).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_14_pos : 0<boundaryFullCoefficient77 3 14 := by

  rw [(boundaryFullCoefficient77Row3Norm 14).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_15_pos : 0<boundaryFullCoefficient77 3 15 := by

  rw [(boundaryFullCoefficient77Row3Norm 15).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_16_pos : 0<boundaryFullCoefficient77 3 16 := by

  rw [(boundaryFullCoefficient77Row3Norm 16).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_17_pos : 0<boundaryFullCoefficient77 3 17 := by

  rw [(boundaryFullCoefficient77Row3Norm 17).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_18_pos : 0<boundaryFullCoefficient77 3 18 := by

  rw [(boundaryFullCoefficient77Row3Norm 18).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_19_pos : 0<boundaryFullCoefficient77 3 19 := by

  rw [(boundaryFullCoefficient77Row3Norm 19).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_20_pos : 0<boundaryFullCoefficient77 3 20 := by

  rw [(boundaryFullCoefficient77Row3Norm 20).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_21_pos : 0<boundaryFullCoefficient77 3 21 := by

  rw [(boundaryFullCoefficient77Row3Norm 21).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_22_pos : 0<boundaryFullCoefficient77 3 22 := by

  rw [(boundaryFullCoefficient77Row3Norm 22).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_23_pos : 0<boundaryFullCoefficient77 3 23 := by

  rw [(boundaryFullCoefficient77Row3Norm 23).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_24_pos : 0<boundaryFullCoefficient77 3 24 := by

  rw [(boundaryFullCoefficient77Row3Norm 24).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_25_pos : 0<boundaryFullCoefficient77 3 25 := by

  rw [(boundaryFullCoefficient77Row3Norm 25).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_26_pos : 0<boundaryFullCoefficient77 3 26 := by

  rw [(boundaryFullCoefficient77Row3Norm 26).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_27_pos : 0<boundaryFullCoefficient77 3 27 := by

  rw [(boundaryFullCoefficient77Row3Norm 27).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_28_pos : 0<boundaryFullCoefficient77 3 28 := by

  rw [(boundaryFullCoefficient77Row3Norm 28).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_29_pos : 0<boundaryFullCoefficient77 3 29 := by

  rw [(boundaryFullCoefficient77Row3Norm 29).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_30_pos : 0<boundaryFullCoefficient77 3 30 := by

  rw [(boundaryFullCoefficient77Row3Norm 30).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_31_pos : 0<boundaryFullCoefficient77 3 31 := by

  rw [(boundaryFullCoefficient77Row3Norm 31).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_32_pos : 0<boundaryFullCoefficient77 3 32 := by

  rw [(boundaryFullCoefficient77Row3Norm 32).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_33_pos : 0<boundaryFullCoefficient77 3 33 := by

  rw [(boundaryFullCoefficient77Row3Norm 33).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_34_pos : 0<boundaryFullCoefficient77 3 34 := by

  rw [(boundaryFullCoefficient77Row3Norm 34).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_35_pos : 0<boundaryFullCoefficient77 3 35 := by

  rw [(boundaryFullCoefficient77Row3Norm 35).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_3_36_pos : 0<boundaryFullCoefficient77 3 36 := by

  rw [(boundaryFullCoefficient77Row3Norm 36).property]

  norm_num [boundaryFullCoefficient77Row3Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


end

end HTGeometry.ThetaRatioInfinity
