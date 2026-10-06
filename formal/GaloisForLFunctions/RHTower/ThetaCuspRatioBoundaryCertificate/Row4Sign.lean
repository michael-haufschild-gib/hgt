import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Row4Norms

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

open HTGeometry.EvenCompactBernstein

def boundaryFullCoefficient77Row4Norm (B : ℕ) : {c : ℝ // boundaryFullCoefficient77 4 B=c} := by

  have he : boundaryFullCoefficient77 4 B=boundaryFullCoefficient77 4 B := rfl

  conv at he =>

    rhs

    dsimp only [boundaryFullCoefficient77]

    rw [(boundaryLowCoefficient77Row4Norm B).property,
      (boundaryReCoefficient77_0Row4Norm B).property,
      (boundaryReCoefficient77_1Row4Norm B).property,
      (boundaryReCoefficient77_2Row4Norm B).property,
      (boundaryReCoefficient77_3Row4Norm B).property,
      (boundaryReCoefficient77_4Row4Norm B).property,
      (boundaryReCoefficient77_5Row4Norm B).property,
      (boundaryReCoefficient77_6Row4Norm B).property,
      (boundaryReCoefficient77_7Row4Norm B).property,
      (boundaryReCoefficient77_8Row4Norm B).property,
      (boundaryReCoefficient77_9Row4Norm B).property,
      (boundaryReCoefficient77_10Row4Norm B).property,
      (boundaryReCoefficient77_11Row4Norm B).property,
      (boundaryReCoefficient77_12Row4Norm B).property,
      (boundaryReCoefficient77_13Row4Norm B).property,
      (boundaryReCoefficient77_14Row4Norm B).property,
      (boundaryReCoefficient77_15Row4Norm B).property,
      (boundaryReCoefficient77_16Row4Norm B).property,
      (boundaryReCoefficient77_17Row4Norm B).property,
      (boundaryReCoefficient77_18Row4Norm B).property,
      (boundaryReCoefficient77_19Row4Norm B).property,
      (boundaryReCoefficient77_20Row4Norm B).property,
      (boundaryReCoefficient77_21Row4Norm B).property,
      (boundaryReCoefficient77_22Row4Norm B).property,
      (boundaryImCoefficient77_0Row4Norm B).property,
      (boundaryImCoefficient77_1Row4Norm B).property,
      (boundaryImCoefficient77_2Row4Norm B).property,
      (boundaryImCoefficient77_3Row4Norm B).property,
      (boundaryImCoefficient77_4Row4Norm B).property,
      (boundaryImCoefficient77_5Row4Norm B).property,
      (boundaryImCoefficient77_6Row4Norm B).property,
      (boundaryImCoefficient77_7Row4Norm B).property,
      (boundaryImCoefficient77_8Row4Norm B).property,
      (boundaryImCoefficient77_9Row4Norm B).property,
      (boundaryImCoefficient77_10Row4Norm B).property,
      (boundaryImCoefficient77_11Row4Norm B).property,
      (boundaryImCoefficient77_12Row4Norm B).property,
      (boundaryImCoefficient77_13Row4Norm B).property,
      (boundaryImCoefficient77_14Row4Norm B).property,
      (boundaryImCoefficient77_15Row4Norm B).property,
      (boundaryImCoefficient77_16Row4Norm B).property,
      (boundaryImCoefficient77_17Row4Norm B).property,
      (boundaryImCoefficient77_18Row4Norm B).property,
      (boundaryImCoefficient77_19Row4Norm B).property,
      (boundaryImCoefficient77_20Row4Norm B).property,
      (boundaryImCoefficient77_21Row4Norm B).property]

    dsimp only [boundaryLowCoefficient77Row4Norm,boundaryReCoefficient77_0Row4Norm,boundaryReCoefficient77_1Row4Norm,boundaryReCoefficient77_2Row4Norm,boundaryReCoefficient77_3Row4Norm,boundaryReCoefficient77_4Row4Norm,boundaryReCoefficient77_5Row4Norm,boundaryReCoefficient77_6Row4Norm,boundaryReCoefficient77_7Row4Norm,boundaryReCoefficient77_8Row4Norm,boundaryReCoefficient77_9Row4Norm,boundaryReCoefficient77_10Row4Norm,boundaryReCoefficient77_11Row4Norm,boundaryReCoefficient77_12Row4Norm,boundaryReCoefficient77_13Row4Norm,boundaryReCoefficient77_14Row4Norm,boundaryReCoefficient77_15Row4Norm,boundaryReCoefficient77_16Row4Norm,boundaryReCoefficient77_17Row4Norm,boundaryReCoefficient77_18Row4Norm,boundaryReCoefficient77_19Row4Norm,boundaryReCoefficient77_20Row4Norm,boundaryReCoefficient77_21Row4Norm,boundaryReCoefficient77_22Row4Norm,boundaryImCoefficient77_0Row4Norm,boundaryImCoefficient77_1Row4Norm,boundaryImCoefficient77_2Row4Norm,boundaryImCoefficient77_3Row4Norm,boundaryImCoefficient77_4Row4Norm,boundaryImCoefficient77_5Row4Norm,boundaryImCoefficient77_6Row4Norm,boundaryImCoefficient77_7Row4Norm,boundaryImCoefficient77_8Row4Norm,boundaryImCoefficient77_9Row4Norm,boundaryImCoefficient77_10Row4Norm,boundaryImCoefficient77_11Row4Norm,boundaryImCoefficient77_12Row4Norm,boundaryImCoefficient77_13Row4Norm,boundaryImCoefficient77_14Row4Norm,boundaryImCoefficient77_15Row4Norm,boundaryImCoefficient77_16Row4Norm,boundaryImCoefficient77_17Row4Norm,boundaryImCoefficient77_18Row4Norm,boundaryImCoefficient77_19Row4Norm,boundaryImCoefficient77_20Row4Norm,boundaryImCoefficient77_21Row4Norm]

    ring_nf (config := {mode := .raw})

  exact ⟨_,he⟩


theorem boundaryFullCoefficient77_4_0_pos : 0<boundaryFullCoefficient77 4 0 := by

  rw [(boundaryFullCoefficient77Row4Norm 0).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_1_pos : 0<boundaryFullCoefficient77 4 1 := by

  rw [(boundaryFullCoefficient77Row4Norm 1).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_2_pos : 0<boundaryFullCoefficient77 4 2 := by

  rw [(boundaryFullCoefficient77Row4Norm 2).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_3_pos : 0<boundaryFullCoefficient77 4 3 := by

  rw [(boundaryFullCoefficient77Row4Norm 3).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_4_pos : 0<boundaryFullCoefficient77 4 4 := by

  rw [(boundaryFullCoefficient77Row4Norm 4).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_5_pos : 0<boundaryFullCoefficient77 4 5 := by

  rw [(boundaryFullCoefficient77Row4Norm 5).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_6_pos : 0<boundaryFullCoefficient77 4 6 := by

  rw [(boundaryFullCoefficient77Row4Norm 6).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_7_pos : 0<boundaryFullCoefficient77 4 7 := by

  rw [(boundaryFullCoefficient77Row4Norm 7).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_8_pos : 0<boundaryFullCoefficient77 4 8 := by

  rw [(boundaryFullCoefficient77Row4Norm 8).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_9_pos : 0<boundaryFullCoefficient77 4 9 := by

  rw [(boundaryFullCoefficient77Row4Norm 9).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_10_pos : 0<boundaryFullCoefficient77 4 10 := by

  rw [(boundaryFullCoefficient77Row4Norm 10).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_11_pos : 0<boundaryFullCoefficient77 4 11 := by

  rw [(boundaryFullCoefficient77Row4Norm 11).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_12_pos : 0<boundaryFullCoefficient77 4 12 := by

  rw [(boundaryFullCoefficient77Row4Norm 12).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_13_pos : 0<boundaryFullCoefficient77 4 13 := by

  rw [(boundaryFullCoefficient77Row4Norm 13).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_14_pos : 0<boundaryFullCoefficient77 4 14 := by

  rw [(boundaryFullCoefficient77Row4Norm 14).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_15_pos : 0<boundaryFullCoefficient77 4 15 := by

  rw [(boundaryFullCoefficient77Row4Norm 15).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_16_pos : 0<boundaryFullCoefficient77 4 16 := by

  rw [(boundaryFullCoefficient77Row4Norm 16).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_17_pos : 0<boundaryFullCoefficient77 4 17 := by

  rw [(boundaryFullCoefficient77Row4Norm 17).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_18_pos : 0<boundaryFullCoefficient77 4 18 := by

  rw [(boundaryFullCoefficient77Row4Norm 18).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_19_pos : 0<boundaryFullCoefficient77 4 19 := by

  rw [(boundaryFullCoefficient77Row4Norm 19).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_20_pos : 0<boundaryFullCoefficient77 4 20 := by

  rw [(boundaryFullCoefficient77Row4Norm 20).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_21_pos : 0<boundaryFullCoefficient77 4 21 := by

  rw [(boundaryFullCoefficient77Row4Norm 21).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_22_pos : 0<boundaryFullCoefficient77 4 22 := by

  rw [(boundaryFullCoefficient77Row4Norm 22).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_23_pos : 0<boundaryFullCoefficient77 4 23 := by

  rw [(boundaryFullCoefficient77Row4Norm 23).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_24_pos : 0<boundaryFullCoefficient77 4 24 := by

  rw [(boundaryFullCoefficient77Row4Norm 24).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_25_pos : 0<boundaryFullCoefficient77 4 25 := by

  rw [(boundaryFullCoefficient77Row4Norm 25).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_26_pos : 0<boundaryFullCoefficient77 4 26 := by

  rw [(boundaryFullCoefficient77Row4Norm 26).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_27_pos : 0<boundaryFullCoefficient77 4 27 := by

  rw [(boundaryFullCoefficient77Row4Norm 27).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_28_pos : 0<boundaryFullCoefficient77 4 28 := by

  rw [(boundaryFullCoefficient77Row4Norm 28).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_29_pos : 0<boundaryFullCoefficient77 4 29 := by

  rw [(boundaryFullCoefficient77Row4Norm 29).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_30_pos : 0<boundaryFullCoefficient77 4 30 := by

  rw [(boundaryFullCoefficient77Row4Norm 30).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_31_pos : 0<boundaryFullCoefficient77 4 31 := by

  rw [(boundaryFullCoefficient77Row4Norm 31).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_32_pos : 0<boundaryFullCoefficient77 4 32 := by

  rw [(boundaryFullCoefficient77Row4Norm 32).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_33_pos : 0<boundaryFullCoefficient77 4 33 := by

  rw [(boundaryFullCoefficient77Row4Norm 33).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_34_pos : 0<boundaryFullCoefficient77 4 34 := by

  rw [(boundaryFullCoefficient77Row4Norm 34).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_35_pos : 0<boundaryFullCoefficient77 4 35 := by

  rw [(boundaryFullCoefficient77Row4Norm 35).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


theorem boundaryFullCoefficient77_4_36_pos : 0<boundaryFullCoefficient77 4 36 := by

  rw [(boundaryFullCoefficient77Row4Norm 36).property]

  norm_num [boundaryFullCoefficient77Row4Norm,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]


end

end HTGeometry.ThetaRatioInfinity
