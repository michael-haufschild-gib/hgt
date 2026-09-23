import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveSharpThinClockCone

open Real Set

namespace RHTower

noncomputable section

def thetaCuspModularParabolicUpperProjectiveClockGap (x : ℝ) : ℝ :=
  let z := thetaCuspModularPositiveLambdaClock x
  (33 / 80 : ℝ) * z + (1 / 12 : ℝ) * z ^ (3 : ℕ) -
    thetaCuspModularNormalizedQuasimodularDrift x

def thetaCuspModularParabolicLowerProjectiveClockGap (x : ℝ) : ℝ :=
  let z := thetaCuspModularPositiveLambdaClock x
  thetaCuspModularNormalizedQuasimodularDrift x -
    ((13 / 32 : ℝ) * z + (1 / 32 : ℝ) * z ^ (3 : ℕ))

def thetaCuspModularParabolicScaleGap (x : ℝ) : ℝ :=
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let z := thetaCuspModularPositiveLambdaClock x
  R ^ (2 : ℕ) - 191 / 10 - (147 / 20 : ℝ) * z ^ (2 : ℕ)

@[simp] theorem thetaCuspModularParabolicUpperProjectiveClockGap_zero :
    thetaCuspModularParabolicUpperProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularParabolicUpperProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

@[simp] theorem thetaCuspModularParabolicLowerProjectiveClockGap_zero :
    thetaCuspModularParabolicLowerProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularParabolicLowerProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

theorem hasDerivAt_thetaCuspModularParabolicUpperProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularParabolicUpperProjectiveClockGap
      ((33 / 80 + thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ) / 4 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ))) -
        (3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ (2 : ℕ) / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) x := by
  have hz := hasDerivAt_thetaCuspModularPositiveLambdaClock x
  have hv := hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x
  have h := ((hz.const_mul (33 / 80 : ℝ)).add
    ((hz.pow 3).const_mul (1 / 12 : ℝ))).sub hv
  change HasDerivAt
    (fun y => (33 / 80 : ℝ) * thetaCuspModularPositiveLambdaClock y +
      (1 / 12 : ℝ) * thetaCuspModularPositiveLambdaClock y ^ (3 : ℕ) -
        thetaCuspModularNormalizedQuasimodularDrift y) _ x
  exact h.congr_deriv (by ring)

theorem hasDerivAt_thetaCuspModularParabolicLowerProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularParabolicLowerProjectiveClockGap
      ((3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ (2 : ℕ) / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re -
        (13 / 32 + 3 * thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ) / 32 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ)))) x := by
  have hz := hasDerivAt_thetaCuspModularPositiveLambdaClock x
  have hv := hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x
  have h := hv.sub ((hz.const_mul (13 / 32 : ℝ)).add
    ((hz.pow 3).const_mul (1 / 32 : ℝ)))
  change HasDerivAt
    (fun y => thetaCuspModularNormalizedQuasimodularDrift y -
      ((13 / 32 : ℝ) * thetaCuspModularPositiveLambdaClock y +
        (1 / 32 : ℝ) * thetaCuspModularPositiveLambdaClock y ^ (3 : ℕ))) _ x
  exact h.congr_deriv (by ring)

theorem deriv_thetaCuspModularParabolicUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularParabolicUpperProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let X := R ^ (2 : ℕ)
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  let S := (thetaCuspModularDrift x).re
  have hR : 0 < R := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hX : (191 / 10 : ℝ) < X := by
    simpa only [X, R] using nineteen_point_one_lt_thetaCuspModularScale_sq_of_pos hx0
  have hXpos : 0 < X := lt_trans (by norm_num) hX
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hzupper : z < (3 / 10 : ℝ) := by
    simpa only [z, thetaCuspModularPositiveLambdaClock] using
      neg_thetaCuspModularODEState_Z_re_lt_three_tenths hx0 hx1
  have hvlower : (13 / 32 : ℝ) * z < v := by
    simpa only [z, v] using
      (thetaCuspModularProjectiveClocks_mem_sharpThinCone hx0 hx1).1
  have hvz : v < z := by
    have hvupper := (thetaCuspModularProjectiveClocks_mem_sharpThinCone hx0 hx1).2
    nlinarith
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using
      thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hdiffpos : 0 < z - v := by linarith
  have hdiffupper : z - v < (19 / 32 : ℝ) * z := by linarith
  have hdiffsq : (z - v) ^ (2 : ℕ) < ((19 / 32 : ℝ) * z) ^ (2 : ℕ) := by
    nlinarith
  have hSsq : S ^ (2 : ℕ) < X * ((19 / 32 : ℝ) * z) ^ (2 : ℕ) := by
    rw [hS]
    dsimp only [X]
    nlinarith [mul_pos (pow_pos hR 2) (sub_pos.mpr hdiffsq)]
  have ht : z ^ (2 : ℕ) < (9 / 100 : ℝ) := by nlinarith
  have ht0 : 0 ≤ z ^ (2 : ℕ) := sq_nonneg z
  have ht2 : (z ^ (2 : ℕ)) ^ (2 : ℕ) < (9 / 100 : ℝ) ^ (2 : ℕ) := by
    exact (sq_lt_sq₀ ht0 (by norm_num)).2 ht
  have hcorner :
      (30 / 191 : ℝ) <
        13 / 80 - (461 / 15360 : ℝ) * (9 / 100) - (9 / 100 : ℝ) ^ (2 : ℕ) / 4 := by
    norm_num
  have hH :
      (30 / 191 : ℝ) <
        (13 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (1 - z ^ (2 : ℕ)) -
          ((19 / 32 : ℝ) * z) ^ (2 : ℕ) / 3 := by
    nlinarith
  have hHpos : 0 <
      (13 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (1 - z ^ (2 : ℕ)) -
        ((19 / 32 : ℝ) * z) ^ (2 : ℕ) / 3 :=
    lt_trans (by norm_num) hH
  have hmain : 3 < X *
      ((13 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (1 - z ^ (2 : ℕ)) -
        ((19 / 32 : ℝ) * z) ^ (2 : ℕ) / 3) := by
    calc
      3 = (191 / 10 : ℝ) * (30 / 191) := by norm_num
      _ < X * (30 / 191 : ℝ) := mul_lt_mul_of_pos_right hX (by norm_num)
      _ < X * ((13 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (1 - z ^ (2 : ℕ)) -
          ((19 / 32 : ℝ) * z) ^ (2 : ℕ) / 3) := mul_lt_mul_of_pos_left hH hXpos
  rw [(hasDerivAt_thetaCuspModularParabolicUpperProjectiveClockGap x).deriv]
  change 0 < (33 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (R * (1 - z ^ (2 : ℕ))) -
    (3 + thetaCuspModularGapAmplitude x / 4 + S ^ (2 : ℕ) / 3) / R
  have hgap : thetaCuspModularGapAmplitude x = X * (1 - z ^ (2 : ℕ)) := by
    dsimp only [thetaCuspModularGapAmplitude, X, R, z,
      thetaCuspModularPositiveLambdaClock]
    ring
  rw [hgap]
  have heq :
      (33 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (R * (1 - z ^ (2 : ℕ))) -
          (3 + X * (1 - z ^ (2 : ℕ)) / 4 + S ^ (2 : ℕ) / 3) / R =
        (X * (13 / 80 + z ^ (2 : ℕ) / 4 : ℝ) * (1 - z ^ (2 : ℕ)) - 3 - S ^ (2 : ℕ) / 3) / R := by
    field_simp [hR.ne']
    dsimp only [X]
    ring
  rw [heq]
  apply div_pos _ hR
  nlinarith

theorem thetaCuspModularParabolicUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularParabolicUpperProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularParabolicUpperProjectiveClockGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularParabolicUpperProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularParabolicUpperProjectiveClockGap_pos
        hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  simpa using h

theorem thetaCuspModularNormalizedQuasimodularDrift_lt_twentyOne_fiftieths_clock
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    thetaCuspModularNormalizedQuasimodularDrift x <
      (21 / 50 : ℝ) * thetaCuspModularPositiveLambdaClock x := by
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hzupper : z < (3 / 10 : ℝ) := by
    simpa only [z, thetaCuspModularPositiveLambdaClock] using
      neg_thetaCuspModularODEState_Z_re_lt_three_tenths hx0 hx1
  have hgap := thetaCuspModularParabolicUpperProjectiveClockGap_pos hx0 hx1
  change 0 < (33 / 80 : ℝ) * z + (1 / 12 : ℝ) * z ^ (3 : ℕ) - v at hgap
  change v < (21 / 50 : ℝ) * z
  have hcoef : (33 / 80 + z ^ (2 : ℕ) / 12 : ℝ) < 21 / 50 := by
    nlinarith [sq_nonneg z]
  nlinarith

theorem deriv_thetaCuspModularParabolicLowerProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularParabolicLowerProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let X := R ^ (2 : ℕ)
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  let S := (thetaCuspModularDrift x).re
  let A := thetaCuspModularGapAmplitude x
  have hR : 0 < R := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hXpos : 0 < X := sq_pos_of_pos hR
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hvupper : v < (21 / 50 : ℝ) * z := by
    simpa only [v, z] using
      thetaCuspModularNormalizedQuasimodularDrift_lt_twentyOne_fiftieths_clock hx0 hx1
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using
      thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hdiff : (29 / 50 : ℝ) * z < z - v := by linarith
  have hdiffsq : ((29 / 50 : ℝ) * z) ^ (2 : ℕ) < (z - v) ^ (2 : ℕ) := by
    nlinarith
  have hSsq : X * ((29 / 50 : ℝ) * z) ^ (2 : ℕ) < S ^ (2 : ℕ) := by
    rw [hS]
    dsimp only [X]
    nlinarith [mul_pos (pow_pos hR 2) (sub_pos.mpr hdiffsq)]
  have hA : A < (96 / 5 : ℝ) := by
    simpa only [A] using thetaCuspModularGapAmplitude_lt_ninetySix_fifths_of_pos hx0
  have hbase : 0 < 3 - (5 / 32 : ℝ) * A := by nlinarith
  have hKpos : 0 < X * z ^ (2 : ℕ) := mul_pos hXpos (sq_pos_of_pos hz)
  have hcoef : (3 / 32 : ℝ) < 841 / 7500 := by norm_num
  have hsmall :
      (3 / 32 : ℝ) * (X * z ^ (2 : ℕ)) * (1 - z ^ (2 : ℕ)) <
        (3 / 32 : ℝ) * (X * z ^ (2 : ℕ)) := by
    nlinarith [sq_pos_of_pos hz, mul_pos (by norm_num : (0 : ℝ) < 3 / 32) hKpos]
  have hcoefmul :
      (3 / 32 : ℝ) * (X * z ^ (2 : ℕ)) <
        (841 / 7500 : ℝ) * (X * z ^ (2 : ℕ)) := by
    nlinarith [mul_pos (sub_pos.mpr hcoef) hKpos]
  have hSthird :
      (841 / 7500 : ℝ) * (X * z ^ (2 : ℕ)) < S ^ (2 : ℕ) / 3 := by
    nlinarith [hSsq]
  have htail :
      (3 / 32 : ℝ) * X * z ^ (2 : ℕ) * (1 - z ^ (2 : ℕ)) < S ^ (2 : ℕ) / 3 := by
    calc
      (3 / 32 : ℝ) * X * z ^ (2 : ℕ) * (1 - z ^ (2 : ℕ)) =
          (3 / 32 : ℝ) * (X * z ^ (2 : ℕ)) * (1 - z ^ (2 : ℕ)) := by ring
      _ < (3 / 32 : ℝ) * (X * z ^ (2 : ℕ)) := hsmall
      _ < (841 / 7500 : ℝ) * (X * z ^ (2 : ℕ)) := hcoefmul
      _ < S ^ (2 : ℕ) / 3 := hSthird
  rw [(hasDerivAt_thetaCuspModularParabolicLowerProjectiveClockGap x).deriv]
  change 0 < (3 + A / 4 + S ^ (2 : ℕ) / 3) / R -
    (13 / 32 + 3 * z ^ (2 : ℕ) / 32 : ℝ) * (R * (1 - z ^ (2 : ℕ)))
  have hgap : A = X * (1 - z ^ (2 : ℕ)) := by
    dsimp only [A, thetaCuspModularGapAmplitude, X, R, z,
      thetaCuspModularPositiveLambdaClock]
    ring
  have heq :
      (3 + A / 4 + S ^ (2 : ℕ) / 3) / R -
          (13 / 32 + 3 * z ^ (2 : ℕ) / 32 : ℝ) * (R * (1 - z ^ (2 : ℕ))) =
        (3 - (5 / 32 : ℝ) * A + S ^ (2 : ℕ) / 3 -
          (3 / 32 : ℝ) * X * z ^ (2 : ℕ) * (1 - z ^ (2 : ℕ))) / R := by
    field_simp [hR.ne']
    rw [hgap]
    dsimp only [X]
    ring
  rw [heq]
  apply div_pos _ hR
  nlinarith

theorem thetaCuspModularParabolicLowerProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularParabolicLowerProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularParabolicLowerProjectiveClockGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularParabolicLowerProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularParabolicLowerProjectiveClockGap_pos
        hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  simpa using h

theorem hasDerivAt_thetaCuspModularParabolicScaleGap (x : ℝ) :
    HasDerivAt thetaCuspModularParabolicScaleGap
      (-(4 / 3 : ℝ) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ (2 : ℕ) *
          (thetaCuspModularDrift x).re -
        (147 / 10 : ℝ) * thetaCuspModularPositiveLambdaClock x *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ)))) x := by
  have hR := hasDerivAt_thetaCuspModularODEState_R_re x
  have hz := hasDerivAt_thetaCuspModularPositiveLambdaClock x
  have hc : HasDerivAt (fun _ : ℝ => (191 / 10 : ℝ)) 0 x := hasDerivAt_const x _
  have h := ((hR.pow 2).sub hc).sub ((hz.pow 2).const_mul (147 / 20 : ℝ))
  change HasDerivAt
    (fun y =>
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re ^ (2 : ℕ) -
        191 / 10 - (147 / 20 : ℝ) * thetaCuspModularPositiveLambdaClock y ^ (2 : ℕ)) _ x
  exact h.congr_deriv (by ring)

theorem thetaCuspModularParabolicScaleGap_zero_pos :
    0 < thetaCuspModularParabolicScaleGap 0 := by
  let R : ℝ → ℝ := fun y =>
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re
  have hzero : R 0 ^ (2 : ℕ) = thetaCuspSelfDualModularScale ^ (2 : ℕ) := by
    have hgap := thetaCuspModularGapAmplitude_zero
    simpa [R, thetaCuspModularGapAmplitude,
      thetaCuspModularPositiveLambdaClock] using hgap
  have hscale : (191 / 10 : ℝ) < R 0 ^ (2 : ℕ) := by
    rw [hzero]
    exact thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  simpa [thetaCuspModularParabolicScaleGap, R] using hscale

theorem deriv_thetaCuspModularParabolicScaleGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularParabolicScaleGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let X := R ^ (2 : ℕ)
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  let S := (thetaCuspModularDrift x).re
  have hR : 0 < R := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hX : (191 / 10 : ℝ) < X := by
    simpa only [X, R] using nineteen_point_one_lt_thetaCuspModularScale_sq_of_pos hx0
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hvupper : v < (21 / 50 : ℝ) * z := by
    simpa only [v, z] using
      thetaCuspModularNormalizedQuasimodularDrift_lt_twentyOne_fiftieths_clock hx0 hx1
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using
      thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hcoef :
      (147 / 10 : ℝ) < (4 / 3 : ℝ) * X * (29 / 50) := by
    have hrat : (147 / 10 : ℝ) < (4 / 3) * (191 / 10) * (29 / 50) := by
      norm_num
    nlinarith [mul_pos (by norm_num : (0 : ℝ) < (4 / 3) * (29 / 50))
      (sub_pos.mpr hX)]
  have hmain :
      (147 / 10 : ℝ) * z * (1 - z ^ (2 : ℕ)) <
        (4 / 3 : ℝ) * X * (z - v) := by
    have hleft :
        (147 / 10 : ℝ) * z * (1 - z ^ (2 : ℕ)) < (147 / 10 : ℝ) * z := by
      nlinarith [sq_pos_of_pos hz]
    have hmid :
        (147 / 10 : ℝ) * z < (4 / 3 : ℝ) * X * (29 / 50) * z := by
      exact mul_lt_mul_of_pos_right hcoef hz
    have hright :
        (4 / 3 : ℝ) * X * (29 / 50) * z <
          (4 / 3 : ℝ) * X * (z - v) := by
      have hXpos : 0 < (4 / 3 : ℝ) * X := by
        exact mul_pos (by norm_num) (lt_trans (by norm_num) hX)
      nlinarith [mul_pos hXpos (sub_pos.mpr (show
        (29 / 50 : ℝ) * z < z - v by linarith))]
    exact hleft.trans (hmid.trans hright)
  rw [(hasDerivAt_thetaCuspModularParabolicScaleGap x).deriv]
  change 0 < -(4 / 3 : ℝ) * X * S -
    (147 / 10 : ℝ) * z * (R * (1 - z ^ (2 : ℕ)))
  rw [hS]
  nlinarith [mul_pos hR (sub_pos.mpr hmain)]

theorem thetaCuspModularParabolicScaleGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularParabolicScaleGap x := by
  have hmono : StrictMonoOn thetaCuspModularParabolicScaleGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularParabolicScaleGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularParabolicScaleGap_pos hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  exact thetaCuspModularParabolicScaleGap_zero_pos.trans h

theorem thetaCuspModularProjectiveClocks_mem_parabolicThinCone
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
    let z := thetaCuspModularPositiveLambdaClock x
    let v := thetaCuspModularNormalizedQuasimodularDrift x
    (13 / 32 + z ^ (2 : ℕ) / 32 : ℝ) * z < v ∧
      v < (33 / 80 + z ^ (2 : ℕ) / 12 : ℝ) * z ∧
      (191 / 10 + (147 / 20 : ℝ) * z ^ (2 : ℕ)) < R ^ (2 : ℕ) := by
  dsimp only
  constructor
  · have h := thetaCuspModularParabolicLowerProjectiveClockGap_pos hx0 hx1
    change 0 < thetaCuspModularNormalizedQuasimodularDrift x -
      ((13 / 32 : ℝ) * thetaCuspModularPositiveLambdaClock x +
        (1 / 32 : ℝ) * thetaCuspModularPositiveLambdaClock x ^ (3 : ℕ)) at h
    nlinarith
  constructor
  · have h := thetaCuspModularParabolicUpperProjectiveClockGap_pos hx0 hx1
    change 0 < (33 / 80 : ℝ) * thetaCuspModularPositiveLambdaClock x +
      (1 / 12 : ℝ) * thetaCuspModularPositiveLambdaClock x ^ (3 : ℕ) -
        thetaCuspModularNormalizedQuasimodularDrift x at h
    nlinarith
  · have h := thetaCuspModularParabolicScaleGap_pos hx0 hx1
    change 0 <
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ (2 : ℕ) -
        191 / 10 - (147 / 20 : ℝ) * thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ) at h
    nlinarith

end

end RHTower
