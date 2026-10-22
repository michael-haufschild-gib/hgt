import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthProjectiveParabolicClockCone

open Real Set

namespace RHTower

noncomputable section

def thetaCuspModularRefinedParabolicUpperProjectiveClockGap (x : ℝ) : ℝ :=
  let z := thetaCuspModularPositiveLambdaClock x
  (33 / 80 : ℝ) * z + (1 / 16 : ℝ) * z ^ (3 : ℕ) -
    thetaCuspModularNormalizedQuasimodularDrift x

def thetaCuspModularRefinedParabolicScaleGap (x : ℝ) : ℝ :=
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let z := thetaCuspModularPositiveLambdaClock x
  R ^ (2 : ℕ) - 191 / 10 - (37 / 5 : ℝ) * z ^ (2 : ℕ)

@[simp] theorem thetaCuspModularRefinedParabolicUpperProjectiveClockGap_zero :
    thetaCuspModularRefinedParabolicUpperProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularRefinedParabolicUpperProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

theorem hasDerivAt_thetaCuspModularRefinedParabolicUpperProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularRefinedParabolicUpperProjectiveClockGap
      ((33 / 80 + 3 * thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ) / 16 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ))) -
        (3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ (2 : ℕ) / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) x := by
  have hz := hasDerivAt_thetaCuspModularPositiveLambdaClock x
  have hv := hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x
  have h := ((hz.const_mul (33 / 80 : ℝ)).add
    ((hz.pow 3).const_mul (1 / 16 : ℝ))).sub hv
  change HasDerivAt
    (fun y => (33 / 80 : ℝ) * thetaCuspModularPositiveLambdaClock y +
      (1 / 16 : ℝ) * thetaCuspModularPositiveLambdaClock y ^ (3 : ℕ) -
        thetaCuspModularNormalizedQuasimodularDrift y) _ x
  exact h.congr_deriv (by ring)

theorem deriv_thetaCuspModularRefinedParabolicUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularRefinedParabolicUpperProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let X := R ^ (2 : ℕ)
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  let S := (thetaCuspModularDrift x).re
  have hR : 0 < R := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hXpos : 0 < X := sq_pos_of_pos hR
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hzupper : z < (3 / 10 : ℝ) := by
    simpa only [z, thetaCuspModularPositiveLambdaClock] using
      neg_thetaCuspModularODEState_Z_re_lt_three_tenths hx0 hx1
  have hcone := thetaCuspModularProjectiveClocks_mem_parabolicThinCone hx0 hx1
  have hvlower : (13 / 32 + z ^ (2 : ℕ) / 32 : ℝ) * z < v := by
    simpa only [z, v, R] using hcone.1
  have hXfloor : (191 / 10 + (147 / 20 : ℝ) * z ^ (2 : ℕ)) < X := by
    simpa only [z, v, R, X] using hcone.2.2
  have hvz : v < z := by
    have hvupper : v < (33 / 80 + z ^ (2 : ℕ) / 12 : ℝ) * z := by
      simpa only [z, v, R] using hcone.2.1
    nlinarith [sq_nonneg z]
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using
      thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hdiffpos : 0 < z - v := by linarith
  have hdiffupper : z - v < (19 / 32 : ℝ) * z := by
    nlinarith [sq_nonneg z]
  have hdiffsq : (z - v) ^ (2 : ℕ) < ((19 / 32 : ℝ) * z) ^ (2 : ℕ) := by
    nlinarith
  have hSsq : S ^ (2 : ℕ) < X * ((19 / 32 : ℝ) * z) ^ (2 : ℕ) := by
    rw [hS]
    dsimp only [X]
    nlinarith [mul_pos (pow_pos hR 2) (sub_pos.mpr hdiffsq)]
  have ht : z ^ (2 : ℕ) < (9 / 100 : ℝ) := by nlinarith
  have ht0 : 0 ≤ z ^ (2 : ℕ) := sq_nonneg z
  have ht2 : (z ^ (2 : ℕ)) ^ (2 : ℕ) < (9 / 100 : ℝ) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ ht ht0 (by norm_num)
  have ht3 : (z ^ (2 : ℕ)) ^ (3 : ℕ) < (9 / 100 : ℝ) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ ht ht0 (by norm_num)
  have hHcorner : 0 <
      (13 / 80 : ℝ) - (1421 / 15360 : ℝ) * (9 / 100) -
        (3 / 16 : ℝ) * (9 / 100) ^ (2 : ℕ) := by
    norm_num
  have hHpos : 0 <
      (13 / 80 : ℝ) - (1421 / 15360 : ℝ) * z ^ (2 : ℕ) -
        (3 / 16 : ℝ) * (z ^ (2 : ℕ)) ^ (2 : ℕ) := by
    nlinarith
  have hcorner : 3 <
      ((191 / 10 : ℝ) + (147 / 20 : ℝ) * (9 / 100)) *
        ((13 / 80 : ℝ) - (1421 / 15360 : ℝ) * (9 / 100) -
          (3 / 16 : ℝ) * (9 / 100) ^ (2 : ℕ)) := by
    norm_num
  have hfloor : 3 <
      ((191 / 10 : ℝ) + (147 / 20 : ℝ) * z ^ (2 : ℕ)) *
        ((13 / 80 : ℝ) - (1421 / 15360 : ℝ) * z ^ (2 : ℕ) -
          (3 / 16 : ℝ) * (z ^ (2 : ℕ)) ^ (2 : ℕ)) := by
    nlinarith
  have hmain : 3 < X *
      ((13 / 80 + 3 * z ^ (2 : ℕ) / 16 : ℝ) * (1 - z ^ (2 : ℕ)) -
        ((19 / 32 : ℝ) * z) ^ (2 : ℕ) / 3) := by
    have hidentity :
        ((13 / 80 + 3 * z ^ (2 : ℕ) / 16 : ℝ) * (1 - z ^ (2 : ℕ)) -
            ((19 / 32 : ℝ) * z) ^ (2 : ℕ) / 3) =
          (13 / 80 : ℝ) - (1421 / 15360 : ℝ) * z ^ (2 : ℕ) -
            (3 / 16 : ℝ) * (z ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    rw [hidentity]
    nlinarith [mul_pos (sub_pos.mpr hXfloor) hHpos]
  rw [(hasDerivAt_thetaCuspModularRefinedParabolicUpperProjectiveClockGap x).deriv]
  change 0 < (33 / 80 + 3 * z ^ (2 : ℕ) / 16 : ℝ) * (R * (1 - z ^ (2 : ℕ))) -
    (3 + thetaCuspModularGapAmplitude x / 4 + S ^ (2 : ℕ) / 3) / R
  have hgap : thetaCuspModularGapAmplitude x = X * (1 - z ^ (2 : ℕ)) := by
    dsimp only [thetaCuspModularGapAmplitude, X, R, z,
      thetaCuspModularPositiveLambdaClock]
    ring
  rw [hgap]
  have heq :
      (33 / 80 + 3 * z ^ (2 : ℕ) / 16 : ℝ) * (R * (1 - z ^ (2 : ℕ))) -
          (3 + X * (1 - z ^ (2 : ℕ)) / 4 + S ^ (2 : ℕ) / 3) / R =
        (X * (13 / 80 + 3 * z ^ (2 : ℕ) / 16 : ℝ) * (1 - z ^ (2 : ℕ)) - 3 - S ^ (2 : ℕ) / 3) / R := by
    field_simp [hR.ne']
    dsimp only [X]
    ring
  rw [heq]
  apply div_pos _ hR
  nlinarith

theorem thetaCuspModularRefinedParabolicUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularRefinedParabolicUpperProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularRefinedParabolicUpperProjectiveClockGap
      (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularRefinedParabolicUpperProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularRefinedParabolicUpperProjectiveClockGap_pos
        hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  simpa using h

theorem thetaCuspModularNormalizedQuasimodularDrift_lt_sixHundredSixtyNine_sixteenHundredths_clock
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    thetaCuspModularNormalizedQuasimodularDrift x <
      (669 / 1600 : ℝ) * thetaCuspModularPositiveLambdaClock x := by
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hzupper : z < (3 / 10 : ℝ) := by
    simpa only [z, thetaCuspModularPositiveLambdaClock] using
      neg_thetaCuspModularODEState_Z_re_lt_three_tenths hx0 hx1
  have hgap := thetaCuspModularRefinedParabolicUpperProjectiveClockGap_pos hx0 hx1
  change 0 < (33 / 80 : ℝ) * z + (1 / 16 : ℝ) * z ^ (3 : ℕ) - v at hgap
  change v < (669 / 1600 : ℝ) * z
  have hcoef : (33 / 80 + z ^ (2 : ℕ) / 16 : ℝ) < 669 / 1600 := by
    nlinarith [sq_nonneg z]
  nlinarith

theorem hasDerivAt_thetaCuspModularRefinedParabolicScaleGap (x : ℝ) :
    HasDerivAt thetaCuspModularRefinedParabolicScaleGap
      (-(4 / 3 : ℝ) *
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ (2 : ℕ) *
          (thetaCuspModularDrift x).re -
        (74 / 5 : ℝ) * thetaCuspModularPositiveLambdaClock x *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ)))) x := by
  have hR := hasDerivAt_thetaCuspModularODEState_R_re x
  have hz := hasDerivAt_thetaCuspModularPositiveLambdaClock x
  have hc : HasDerivAt (fun _ : ℝ => (191 / 10 : ℝ)) 0 x := hasDerivAt_const x _
  have h := ((hR.pow 2).sub hc).sub ((hz.pow 2).const_mul (37 / 5 : ℝ))
  change HasDerivAt
    (fun y =>
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re ^ (2 : ℕ) -
        191 / 10 - (37 / 5 : ℝ) * thetaCuspModularPositiveLambdaClock y ^ (2 : ℕ)) _ x
  exact h.congr_deriv (by ring)

theorem thetaCuspModularRefinedParabolicScaleGap_zero_pos :
    0 < thetaCuspModularRefinedParabolicScaleGap 0 := by
  let R : ℝ → ℝ := fun y =>
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re
  have hzero : R 0 ^ (2 : ℕ) = thetaCuspSelfDualModularScale ^ (2 : ℕ) := by
    have hgap := thetaCuspModularGapAmplitude_zero
    simpa [R, thetaCuspModularGapAmplitude,
      thetaCuspModularPositiveLambdaClock] using hgap
  have hscale : (191 / 10 : ℝ) < R 0 ^ (2 : ℕ) := by
    rw [hzero]
    exact thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  simpa [thetaCuspModularRefinedParabolicScaleGap, R] using hscale

theorem deriv_thetaCuspModularRefinedParabolicScaleGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularRefinedParabolicScaleGap x := by
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
  have hvupper : v < (669 / 1600 : ℝ) * z := by
    simpa only [v, z] using
      thetaCuspModularNormalizedQuasimodularDrift_lt_sixHundredSixtyNine_sixteenHundredths_clock
        hx0 hx1
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using
      thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hcoef :
      (74 / 5 : ℝ) < (4 / 3 : ℝ) * X * (931 / 1600) := by
    have hrat : (74 / 5 : ℝ) <
        (4 / 3) * (191 / 10) * (931 / 1600) := by
      norm_num
    nlinarith [mul_pos (by norm_num : (0 : ℝ) < (4 / 3) * (931 / 1600))
      (sub_pos.mpr hX)]
  have hmain :
      (74 / 5 : ℝ) * z * (1 - z ^ (2 : ℕ)) <
        (4 / 3 : ℝ) * X * (z - v) := by
    have hleft : (74 / 5 : ℝ) * z * (1 - z ^ (2 : ℕ)) < (74 / 5 : ℝ) * z := by
      nlinarith [sq_pos_of_pos hz]
    have hmid : (74 / 5 : ℝ) * z <
        (4 / 3 : ℝ) * X * (931 / 1600) * z := by
      exact mul_lt_mul_of_pos_right hcoef hz
    have hright : (4 / 3 : ℝ) * X * (931 / 1600) * z <
        (4 / 3 : ℝ) * X * (z - v) := by
      have hXpos : 0 < (4 / 3 : ℝ) * X := by
        exact mul_pos (by norm_num) (lt_trans (by norm_num) hX)
      nlinarith [mul_pos hXpos (sub_pos.mpr (show
        (931 / 1600 : ℝ) * z < z - v by linarith))]
    exact hleft.trans (hmid.trans hright)
  rw [(hasDerivAt_thetaCuspModularRefinedParabolicScaleGap x).deriv]
  change 0 < -(4 / 3 : ℝ) * X * S -
    (74 / 5 : ℝ) * z * (R * (1 - z ^ (2 : ℕ)))
  rw [hS]
  nlinarith [mul_pos hR (sub_pos.mpr hmain)]

theorem thetaCuspModularRefinedParabolicScaleGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularRefinedParabolicScaleGap x := by
  have hmono : StrictMonoOn thetaCuspModularRefinedParabolicScaleGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularRefinedParabolicScaleGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularRefinedParabolicScaleGap_pos hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  exact thetaCuspModularRefinedParabolicScaleGap_zero_pos.trans h

theorem thetaCuspModularProjectiveClocks_mem_refinedParabolicThinCone
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
    let z := thetaCuspModularPositiveLambdaClock x
    let v := thetaCuspModularNormalizedQuasimodularDrift x
    (13 / 32 + z ^ (2 : ℕ) / 32 : ℝ) * z < v ∧
      v < (33 / 80 + z ^ (2 : ℕ) / 16 : ℝ) * z ∧
      (191 / 10 + (37 / 5 : ℝ) * z ^ (2 : ℕ)) < R ^ (2 : ℕ) := by
  dsimp only
  constructor
  · exact (thetaCuspModularProjectiveClocks_mem_parabolicThinCone hx0 hx1).1
  constructor
  · have h := thetaCuspModularRefinedParabolicUpperProjectiveClockGap_pos hx0 hx1
    change 0 < (33 / 80 : ℝ) * thetaCuspModularPositiveLambdaClock x +
      (1 / 16 : ℝ) * thetaCuspModularPositiveLambdaClock x ^ (3 : ℕ) -
        thetaCuspModularNormalizedQuasimodularDrift x at h
    nlinarith
  · have h := thetaCuspModularRefinedParabolicScaleGap_pos hx0 hx1
    change 0 <
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ (2 : ℕ) -
        191 / 10 - (37 / 5 : ℝ) * thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ) at h
    nlinarith

end

end RHTower
