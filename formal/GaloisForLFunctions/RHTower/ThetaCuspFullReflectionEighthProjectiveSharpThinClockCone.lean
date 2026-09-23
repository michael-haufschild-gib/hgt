import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveThinClockCone

open Real Set

namespace RHTower

noncomputable section

def thetaCuspModularSharpLowerProjectiveClockGap (x : ℝ) : ℝ :=
  thetaCuspModularNormalizedQuasimodularDrift x -
    (13 / 32 : ℝ) * thetaCuspModularPositiveLambdaClock x

def thetaCuspModularSharpUpperProjectiveClockGap (x : ℝ) : ℝ :=
  (7 / 16 : ℝ) * thetaCuspModularPositiveLambdaClock x -
    thetaCuspModularNormalizedQuasimodularDrift x

@[simp] theorem thetaCuspModularSharpLowerProjectiveClockGap_zero :
    thetaCuspModularSharpLowerProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularSharpLowerProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

@[simp] theorem thetaCuspModularSharpUpperProjectiveClockGap_zero :
    thetaCuspModularSharpUpperProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularSharpUpperProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

theorem hasDerivAt_thetaCuspModularSharpLowerProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularSharpLowerProjectiveClockGap
      ((3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ (2 : ℕ) / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re -
        (13 / 32 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ)))) x := by
  exact (hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x).sub
    ((hasDerivAt_thetaCuspModularPositiveLambdaClock x).const_mul (13 / 32 : ℝ))

theorem hasDerivAt_thetaCuspModularSharpUpperProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularSharpUpperProjectiveClockGap
      ((7 / 16 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ))) -
        (3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ (2 : ℕ) / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) x := by
  exact ((hasDerivAt_thetaCuspModularPositiveLambdaClock x).const_mul
    (7 / 16 : ℝ)).sub
      (hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x)

theorem thetaCuspModularGapAmplitude_lt_ninetySix_fifths_of_pos
    {x : ℝ} (hx : 0 < x) :
    thetaCuspModularGapAmplitude x < (96 / 5 : ℝ) := by
  have hgap := thetaCuspModularGapAmplitude_lt_selfDual_of_pos hx
  have hself := thetaCuspSelfDualModularScale_sq_lt_projectiveClockThreshold
  have hthreshold : (360000 / 18769 : ℝ) < 96 / 5 := by norm_num
  exact hgap.trans (hself.trans hthreshold)

theorem deriv_thetaCuspModularSharpLowerProjectiveClockGap_pos
    {x : ℝ} (hx : 0 < x) :
    0 < deriv thetaCuspModularSharpLowerProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let A := thetaCuspModularGapAmplitude x
  let S := (thetaCuspModularDrift x).re
  have hR : 0 < R := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hA : A < (96 / 5 : ℝ) := by
    simpa only [A] using thetaCuspModularGapAmplitude_lt_ninetySix_fifths_of_pos hx
  have hgap : A = R ^ (2 : ℕ) * (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ)) := by
    dsimp only [A, R, thetaCuspModularGapAmplitude,
      thetaCuspModularPositiveLambdaClock]
    ring
  rw [(hasDerivAt_thetaCuspModularSharpLowerProjectiveClockGap x).deriv]
  have heq :
      (3 + A / 4 + S ^ (2 : ℕ) / 3) / R -
          (13 / 32 : ℝ) * (R * (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ))) =
        (3 - (5 / 32 : ℝ) * A + S ^ (2 : ℕ) / 3) / R := by
    rw [hgap]
    field_simp [hR.ne']
    ring
  change 0 < (3 + A / 4 + S ^ (2 : ℕ) / 3) / R -
    (13 / 32 : ℝ) * (R * (1 - thetaCuspModularPositiveLambdaClock x ^ (2 : ℕ)))
  rw [heq]
  exact div_pos (by nlinarith [sq_nonneg S]) hR

theorem thetaCuspModularSharpLowerProjectiveClockGap_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspModularSharpLowerProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularSharpLowerProjectiveClockGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularSharpLowerProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularSharpLowerProjectiveClockGap_pos hy'.1
  have h := hmono (by exact ⟨le_rfl, hx.le⟩) (by exact ⟨hx.le, le_rfl⟩) hx
  simpa using h

theorem deriv_thetaCuspModularSharpUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularSharpUpperProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let X := R ^ (2 : ℕ)
  let z := thetaCuspModularPositiveLambdaClock x
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  let S := (thetaCuspModularDrift x).re
  have hR : 0 < R := by simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hX : (191 / 10 : ℝ) < X := by
    simpa only [X, R] using nineteen_point_one_lt_thetaCuspModularScale_sq_of_pos hx0
  have hz : 0 < z := by
    have h := (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).2.2.1
    simpa only [z, thetaCuspModularPositiveLambdaClock,
      three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift] using h
  have hzupper : z < (3 / 10 : ℝ) := by
    simpa only [z, thetaCuspModularPositiveLambdaClock] using
      neg_thetaCuspModularODEState_Z_re_lt_three_tenths hx0 hx1
  have hvlower : (13 / 32 : ℝ) * z < v := by
    simpa only [thetaCuspModularSharpLowerProjectiveClockGap, sub_pos, z, v] using
      thetaCuspModularSharpLowerProjectiveClockGap_pos hx0
  have hvz : v < z := by
    have hsimp := thetaCuspModularNormalizedClocks_mem_strictSimplex hx0
    have hrel := three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift x
    change 3 * thetaCuspModularNormalizedShear x - 2 * v = z at hrel
    have hvt : v < thetaCuspModularNormalizedShear x := by
      simpa only [v] using hsimp.2.1
    nlinarith
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hgap : thetaCuspModularGapAmplitude x = X * (1 - z ^ (2 : ℕ)) := by
    dsimp only [thetaCuspModularGapAmplitude, X, R, z,
      thetaCuspModularPositiveLambdaClock]
    ring
  have hSsq : S ^ (2 : ℕ) < X * ((19 / 32 : ℝ) * z) ^ (2 : ℕ) := by
    rw [hS]
    have hdiffpos : 0 < z - v := by linarith
    have hdiffupper : z - v < (19 / 32 : ℝ) * z := by linarith
    have hdiffsq : (z - v) ^ (2 : ℕ) < ((19 / 32 : ℝ) * z) ^ (2 : ℕ) := by nlinarith
    have hXpos : 0 < X := sq_pos_of_pos hR
    nlinarith
  rw [(hasDerivAt_thetaCuspModularSharpUpperProjectiveClockGap x).deriv]
  have heq :
      (7 / 16 : ℝ) * (R * (1 - z ^ (2 : ℕ))) -
          (3 + thetaCuspModularGapAmplitude x / 4 + S ^ (2 : ℕ) / 3) / R =
        (X * (3 / 16 : ℝ) * (1 - z ^ (2 : ℕ)) - 3 - S ^ (2 : ℕ) / 3) / R := by
    rw [hgap]
    field_simp [hR.ne']
    ring
  change 0 < (7 / 16 : ℝ) * (R * (1 - z ^ (2 : ℕ))) -
    (3 + thetaCuspModularGapAmplitude x / 4 + S ^ (2 : ℕ) / 3) / R
  rw [heq]
  apply div_pos _ hR
  have hcoef : 0 < (3 / 16 : ℝ) - 937 * z ^ (2 : ℕ) / 3072 := by
    nlinarith [sq_nonneg z]
  have hmain : 3 < X * ((3 / 16 : ℝ) - 937 * z ^ (2 : ℕ) / 3072) := by
    have hfloor :
        3 < (191 / 10 : ℝ) *
          ((3 / 16 : ℝ) - 937 * (3 / 10 : ℝ) ^ (2 : ℕ) / 3072) := by
      norm_num
    have hzsq : z ^ (2 : ℕ) < (3 / 10 : ℝ) ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hX) hcoef]
  nlinarith

theorem thetaCuspModularSharpUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularSharpUpperProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularSharpUpperProjectiveClockGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularSharpUpperProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularSharpUpperProjectiveClockGap_pos hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  simpa using h

theorem thetaCuspModularProjectiveClocks_mem_sharpThinCone
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    (13 / 32 : ℝ) * thetaCuspModularPositiveLambdaClock x <
        thetaCuspModularNormalizedQuasimodularDrift x ∧
      thetaCuspModularNormalizedQuasimodularDrift x <
        (7 / 16 : ℝ) * thetaCuspModularPositiveLambdaClock x := by
  constructor
  · simpa [thetaCuspModularSharpLowerProjectiveClockGap, sub_pos] using
      thetaCuspModularSharpLowerProjectiveClockGap_pos hx0
  · simpa [thetaCuspModularSharpUpperProjectiveClockGap, sub_pos] using
      thetaCuspModularSharpUpperProjectiveClockGap_pos hx0 hx1

end

end RHTower

