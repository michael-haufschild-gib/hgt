import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CoefficientRe

import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.CoefficientIm

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryLowCoefficient77 (A B : ℕ) : ℝ :=
  (((((boundaryTermCoefficient77 ((104096251904/531441 : ℝ)) (6-6) 1 0 A B) + (boundaryTermCoefficient77 ((336723968/6561 : ℝ)) (6-6) 2 0 A B)) + ((boundaryTermCoefficient77 ((-1301807104/531441 : ℝ)) (6-6) 3 0 A B) + (boundaryTermCoefficient77 ((-1304204238848/4782969 : ℝ)) (7-6) 1 0 A B))) + (((boundaryTermCoefficient77 ((-47163277312/1594323 : ℝ)) (7-6) 2 0 A B) + (boundaryTermCoefficient77 ((1592262656/1594323 : ℝ)) (7-6) 3 0 A B)) + ((boundaryTermCoefficient77 ((-23604740096/4782969 : ℝ)) (8-6) 2 0 A B) + ((boundaryTermCoefficient77 ((-3967516672/1594323 : ℝ)) (8-6) 3 0 A B) + (boundaryTermCoefficient77 ((692584448/1594323 : ℝ)) (8-6) 4 0 A B))))) + ((((boundaryTermCoefficient77 ((40742912000/4782969 : ℝ)) (9-6) 3 0 A B) + (boundaryTermCoefficient77 ((-4044161024/4782969 : ℝ)) (9-6) 4 0 A B)) + ((boundaryTermCoefficient77 ((-51636723712/14348907 : ℝ)) (10-6) 3 0 A B) + (boundaryTermCoefficient77 ((2856648704/14348907 : ℝ)) (10-6) 4 0 A B))) + (((boundaryTermCoefficient77 ((-92569600/4782969 : ℝ)) (10-6) 5 0 A B) + (boundaryTermCoefficient77 ((1094238208/4782969 : ℝ)) (11-6) 4 0 A B)) + ((boundaryTermCoefficient77 ((323993600/4782969 : ℝ)) (11-6) 5 0 A B) + ((boundaryTermCoefficient77 ((-1133977600/14348907 : ℝ)) (12-6) 5 0 A B) + (boundaryTermCoefficient77 ((3968921600/129140163 : ℝ)) (13-6) 5 0 A B))))))

theorem boundaryLowCoefficient77_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryLowCoefficient77 t v=boundaryLowCore77 (boundaryH77*t) (boundaryS77*v) := by

  unfold boundaryLowCoefficient77

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction ((104096251904/531441 : ℝ)) (6-6) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((336723968/6561 : ℝ)) (6-6) 2 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1301807104/531441 : ℝ)) (6-6) 3 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1304204238848/4782969 : ℝ)) (7-6) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-47163277312/1594323 : ℝ)) (7-6) 2 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1592262656/1594323 : ℝ)) (7-6) 3 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-23604740096/4782969 : ℝ)) (8-6) 2 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-3967516672/1594323 : ℝ)) (8-6) 3 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((692584448/1594323 : ℝ)) (8-6) 4 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((40742912000/4782969 : ℝ)) (9-6) 3 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-4044161024/4782969 : ℝ)) (9-6) 4 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-51636723712/14348907 : ℝ)) (10-6) 3 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((2856648704/14348907 : ℝ)) (10-6) 4 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-92569600/4782969 : ℝ)) (10-6) 5 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((1094238208/4782969 : ℝ)) (11-6) 4 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((323993600/4782969 : ℝ)) (11-6) 5 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((-1133977600/14348907 : ℝ)) (12-6) 5 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction ((3968921600/129140163 : ℝ)) (13-6) 5 0 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryLowCore77]

  ring


def boundaryFullCoefficient77 (A B : ℕ) : ℝ :=
  ((((((boundaryLowCoefficient77 A B) + (boundaryReCoefficient77_0 A B)) + ((boundaryReCoefficient77_1 A B) + ((boundaryReCoefficient77_2 A B) + (boundaryReCoefficient77_3 A B)))) + (((boundaryReCoefficient77_4 A B) + ((boundaryReCoefficient77_5 A B) + (boundaryReCoefficient77_6 A B))) + ((boundaryReCoefficient77_7 A B) + ((boundaryReCoefficient77_8 A B) + (boundaryReCoefficient77_9 A B))))) + ((((boundaryReCoefficient77_10 A B) + ((boundaryReCoefficient77_11 A B) + (boundaryReCoefficient77_12 A B))) + ((boundaryReCoefficient77_13 A B) + ((boundaryReCoefficient77_14 A B) + (boundaryReCoefficient77_15 A B)))) + (((boundaryReCoefficient77_16 A B) + ((boundaryReCoefficient77_17 A B) + (boundaryReCoefficient77_18 A B))) + ((boundaryReCoefficient77_19 A B) + ((boundaryReCoefficient77_20 A B) + (boundaryReCoefficient77_21 A B)))))) + (((((boundaryReCoefficient77_22 A B) + (boundaryImCoefficient77_0 A B)) + ((boundaryImCoefficient77_1 A B) + ((boundaryImCoefficient77_2 A B) + (boundaryImCoefficient77_3 A B)))) + (((boundaryImCoefficient77_4 A B) + ((boundaryImCoefficient77_5 A B) + (boundaryImCoefficient77_6 A B))) + ((boundaryImCoefficient77_7 A B) + ((boundaryImCoefficient77_8 A B) + (boundaryImCoefficient77_9 A B))))) + ((((boundaryImCoefficient77_10 A B) + ((boundaryImCoefficient77_11 A B) + (boundaryImCoefficient77_12 A B))) + ((boundaryImCoefficient77_13 A B) + ((boundaryImCoefficient77_14 A B) + (boundaryImCoefficient77_15 A B)))) + (((boundaryImCoefficient77_16 A B) + ((boundaryImCoefficient77_17 A B) + (boundaryImCoefficient77_18 A B))) + ((boundaryImCoefficient77_19 A B) + ((boundaryImCoefficient77_20 A B) + (boundaryImCoefficient77_21 A B)))))))

theorem boundaryFullCoefficient77_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryFullCoefficient77 t v=boundaryRegularCore77 (boundaryH77*t) (boundaryS77*v) := by

  unfold boundaryFullCoefficient77

  simp only [boundaryBernstein77_add,boundaryLowCoefficient77_reconstruction,boundaryReCoefficient77_0_reconstruction,boundaryReCoefficient77_1_reconstruction,boundaryReCoefficient77_2_reconstruction,boundaryReCoefficient77_3_reconstruction,boundaryReCoefficient77_4_reconstruction,boundaryReCoefficient77_5_reconstruction,boundaryReCoefficient77_6_reconstruction,boundaryReCoefficient77_7_reconstruction,boundaryReCoefficient77_8_reconstruction,boundaryReCoefficient77_9_reconstruction,boundaryReCoefficient77_10_reconstruction,boundaryReCoefficient77_11_reconstruction,boundaryReCoefficient77_12_reconstruction,boundaryReCoefficient77_13_reconstruction,boundaryReCoefficient77_14_reconstruction,boundaryReCoefficient77_15_reconstruction,boundaryReCoefficient77_16_reconstruction,boundaryReCoefficient77_17_reconstruction,boundaryReCoefficient77_18_reconstruction,boundaryReCoefficient77_19_reconstruction,boundaryReCoefficient77_20_reconstruction,boundaryReCoefficient77_21_reconstruction,boundaryReCoefficient77_22_reconstruction,boundaryImCoefficient77_0_reconstruction,boundaryImCoefficient77_1_reconstruction,boundaryImCoefficient77_2_reconstruction,boundaryImCoefficient77_3_reconstruction,boundaryImCoefficient77_4_reconstruction,boundaryImCoefficient77_5_reconstruction,boundaryImCoefficient77_6_reconstruction,boundaryImCoefficient77_7_reconstruction,boundaryImCoefficient77_8_reconstruction,boundaryImCoefficient77_9_reconstruction,boundaryImCoefficient77_10_reconstruction,boundaryImCoefficient77_11_reconstruction,boundaryImCoefficient77_12_reconstruction,boundaryImCoefficient77_13_reconstruction,boundaryImCoefficient77_14_reconstruction,boundaryImCoefficient77_15_reconstruction,boundaryImCoefficient77_16_reconstruction,boundaryImCoefficient77_17_reconstruction,boundaryImCoefficient77_18_reconstruction,boundaryImCoefficient77_19_reconstruction,boundaryImCoefficient77_20_reconstruction,boundaryImCoefficient77_21_reconstruction]

  dsimp only [boundaryRegularCore77,boundaryReHigh77,boundaryImHigh77]

  ring


end

end HTGeometry.ThetaRatioInfinity
