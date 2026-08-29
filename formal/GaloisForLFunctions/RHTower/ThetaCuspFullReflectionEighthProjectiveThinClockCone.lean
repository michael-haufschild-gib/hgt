import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveClockChamber
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Thin projective clock cone for the rank-three theta trajectory

The normalized quasimodular clock `v` and positive modular-lambda clock `z = -Z`
obey the strict rational cone

`(2/5) * z < v < (1/2) * z`

throughout the compact interval left open by native rank-three reflected eighth curvature.
The proof is source-only and computation-free. Lower wall follows from strict decay of modular
discriminant gap below `20`. Upper wall follows from increasing modular scale, existing strict
clock simplex, and independently proved bound `z < 3/10`.

This theorem is trajectory localization only. It does not import or assert any polynomial
certificate for projective-drift positivity.
-/

open Real Set

namespace RHTower

noncomputable section

def thetaCuspModularPositiveLambdaClock (x : ℝ) : ℝ :=
  -(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re

def thetaCuspModularLowerProjectiveClockGap (x : ℝ) : ℝ :=
  thetaCuspModularNormalizedQuasimodularDrift x -
    (2 / 5 : ℝ) * thetaCuspModularPositiveLambdaClock x

def thetaCuspModularUpperProjectiveClockGap (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * thetaCuspModularPositiveLambdaClock x -
    thetaCuspModularNormalizedQuasimodularDrift x

@[simp] theorem thetaCuspModularPositiveLambdaClock_zero :
    thetaCuspModularPositiveLambdaClock 0 = 0 := by
  simp [thetaCuspModularPositiveLambdaClock]

@[simp] theorem thetaCuspModularLowerProjectiveClockGap_zero :
    thetaCuspModularLowerProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularLowerProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

@[simp] theorem thetaCuspModularUpperProjectiveClockGap_zero :
    thetaCuspModularUpperProjectiveClockGap 0 = 0 := by
  simp [thetaCuspModularUpperProjectiveClockGap,
    thetaCuspModularNormalizedQuasimodularDrift_zero]

theorem hasDerivAt_thetaCuspModularPositiveLambdaClock (x : ℝ) :
    HasDerivAt thetaCuspModularPositiveLambdaClock
      ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
        (1 - thetaCuspModularPositiveLambdaClock x ^ 2)) x := by
  have h := (hasDerivAt_thetaCuspModularODEState_Z_re x).neg
  have hfun :
      (-fun y : ℝ =>
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re) =
      (fun y : ℝ =>
        -(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re) := by
    funext y
    rfl
  rw [hfun] at h
  have hcoef :
      -(-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (1 - (thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re ^ 2)) =
        (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
          (1 - (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) ^ 2) := by
    ring
  rw [hcoef] at h
  change HasDerivAt
    (fun y => -(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z y).re)
    ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
      (1 - (-(thetaCuspModularODEState HTGeometry.ModularThetaODEState.Z x).re) ^ 2)) x
  exact h

theorem hasDerivAt_thetaCuspModularLowerProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularLowerProjectiveClockGap
      ((3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ 2 / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re -
        (2 / 5 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ 2))) x := by
  exact (hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x).sub
    ((hasDerivAt_thetaCuspModularPositiveLambdaClock x).const_mul (2 / 5 : ℝ))

theorem hasDerivAt_thetaCuspModularUpperProjectiveClockGap (x : ℝ) :
    HasDerivAt thetaCuspModularUpperProjectiveClockGap
      ((1 / 2 : ℝ) *
          ((thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
            (1 - thetaCuspModularPositiveLambdaClock x ^ 2)) -
        (3 + thetaCuspModularGapAmplitude x / 4 +
            (thetaCuspModularDrift x).re ^ 2 / 3) /
          (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re) x := by
  exact ((hasDerivAt_thetaCuspModularPositiveLambdaClock x).const_mul
    (1 / 2 : ℝ)).sub
      (hasDerivAt_thetaCuspModularNormalizedQuasimodularDrift x)

theorem thetaCuspModularGapAmplitude_lt_twenty_of_pos
    {x : ℝ} (hx : 0 < x) :
    thetaCuspModularGapAmplitude x < 20 := by
  exact (thetaCuspModularGapAmplitude_lt_selfDual_of_pos hx).trans
    thetaCuspSelfDualModularScale_sq_lt_twenty

theorem deriv_thetaCuspModularLowerProjectiveClockGap_pos
    {x : ℝ} (hx : 0 < x) :
    0 < deriv thetaCuspModularLowerProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let A := thetaCuspModularGapAmplitude x
  let S := (thetaCuspModularDrift x).re
  have hR : 0 < R := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos x
  have hA : A < 20 := by
    simpa only [A] using thetaCuspModularGapAmplitude_lt_twenty_of_pos hx
  have hgap : A = R ^ 2 * (1 - thetaCuspModularPositiveLambdaClock x ^ 2) := by
    dsimp only [A, R, thetaCuspModularGapAmplitude,
      thetaCuspModularPositiveLambdaClock]
    ring
  rw [(hasDerivAt_thetaCuspModularLowerProjectiveClockGap x).deriv]
  have heq :
      (3 + A / 4 + S ^ 2 / 3) / R -
          (2 / 5 : ℝ) * (R * (1 - thetaCuspModularPositiveLambdaClock x ^ 2)) =
        (3 - (3 / 20 : ℝ) * A + S ^ 2 / 3) / R := by
    rw [hgap]
    field_simp [hR.ne']
    ring
  change 0 < (3 + A / 4 + S ^ 2 / 3) / R -
    (2 / 5 : ℝ) * (R * (1 - thetaCuspModularPositiveLambdaClock x ^ 2))
  rw [heq]
  exact div_pos (by nlinarith [sq_nonneg S]) hR

theorem thetaCuspModularLowerProjectiveClockGap_pos
    {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspModularLowerProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularLowerProjectiveClockGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularLowerProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularLowerProjectiveClockGap_pos hy'.1
  have h := hmono (by exact ⟨le_rfl, hx.le⟩) (by exact ⟨hx.le, le_rfl⟩) hx
  simpa using h

theorem strictMonoOn_thetaCuspModularODEState_R_re_nonneg :
    StrictMonoOn
      (fun x => (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re)
      (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspModularODEState_R_re x).continuousAt).continuousOn
  · intro x hx
    have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [(hasDerivAt_thetaCuspModularODEState_R_re x).deriv]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (by norm_num)
        (thetaCuspModularODEState_R_re_pos x))
      (thetaCuspModularDrift_re_neg_of_pos hxpos)

theorem nineteen_point_one_lt_thetaCuspModularScale_sq_of_pos
    {x : ℝ} (hx : 0 < x) :
    (191 / 10 : ℝ) <
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re ^ 2 := by
  let R : ℝ → ℝ := fun y =>
    (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R y).re
  have hRmono : R 0 < R x := by
    exact strictMonoOn_thetaCuspModularODEState_R_re_nonneg
      (by simp) (by simp [hx.le]) hx
  have hR0 : 0 < R 0 := by
    simpa only [R] using thetaCuspModularODEState_R_re_pos 0
  have hsq : R 0 ^ 2 < R x ^ 2 := by nlinarith
  have hzero : R 0 ^ 2 = thetaCuspSelfDualModularScale ^ 2 := by
    have hgap := thetaCuspModularGapAmplitude_zero
    simpa [R, thetaCuspModularGapAmplitude,
      thetaCuspModularPositiveLambdaClock] using hgap
  rw [hzero] at hsq
  exact thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.trans hsq

theorem thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda (x : ℝ) :
    (thetaCuspModularDrift x).re =
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re *
        (thetaCuspModularNormalizedQuasimodularDrift x -
          thetaCuspModularPositiveLambdaClock x) := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let v := thetaCuspModularNormalizedQuasimodularDrift x
  let w := thetaCuspModularNormalizedShear x
  let z := thetaCuspModularPositiveLambdaClock x
  have hR : R ≠ 0 := by
    exact (thetaCuspModularODEState_R_re_pos x).ne'
  have hdiff := thetaCuspModularNormalizedQuasimodularDrift_sub_normalizedShear x
  have hz := three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift x
  change v - w = (thetaCuspModularDrift x).re / (3 * R) at hdiff
  change 3 * w - 2 * v = z at hz
  change (thetaCuspModularDrift x).re = R * (v - z)
  field_simp [hR] at hdiff
  calc
    (thetaCuspModularDrift x).re = (v - w) * 3 * R := hdiff.symm
    _ = R * (v - z) := by rw [← hz]; ring

theorem deriv_thetaCuspModularUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < deriv thetaCuspModularUpperProjectiveClockGap x := by
  let R := (thetaCuspModularODEState HTGeometry.ModularThetaODEState.R x).re
  let X := R ^ 2
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
  have hv : 0 < v := by
    simpa only [v] using (thetaCuspModularNormalizedClocks_mem_strictSimplex hx0).1
  have hvz : v < z := by
    have hsimp := thetaCuspModularNormalizedClocks_mem_strictSimplex hx0
    have hrel := three_mul_normalizedShear_sub_two_mul_normalizedQuasimodularDrift x
    change 3 * thetaCuspModularNormalizedShear x - 2 * v = z at hrel
    have hvt : v < thetaCuspModularNormalizedShear x := by
      simpa only [v] using hsimp.2.1
    nlinarith
  have hS : S = R * (v - z) := by
    simpa only [S, R, v, z] using thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda x
  have hgap : thetaCuspModularGapAmplitude x = X * (1 - z ^ 2) := by
    dsimp only [thetaCuspModularGapAmplitude, X, R, z,
      thetaCuspModularPositiveLambdaClock]
    ring
  have hSsq : S ^ 2 < X * z ^ 2 := by
    rw [hS]
    have hdiffsq : (v - z) ^ 2 < z ^ 2 := by nlinarith
    have hXpos : 0 < X := sq_pos_of_pos hR
    nlinarith
  rw [(hasDerivAt_thetaCuspModularUpperProjectiveClockGap x).deriv]
  have heq :
      (1 / 2 : ℝ) * (R * (1 - z ^ 2)) -
          (3 + thetaCuspModularGapAmplitude x / 4 + S ^ 2 / 3) / R =
        (thetaCuspModularGapAmplitude x / 4 - 3 - S ^ 2 / 3) / R := by
    rw [hgap]
    field_simp [hR.ne']
    ring
  change 0 < (1 / 2 : ℝ) * (R * (1 - z ^ 2)) -
    (3 + thetaCuspModularGapAmplitude x / 4 + S ^ 2 / 3) / R
  rw [heq]
  apply div_pos _ hR
  rw [hgap]
  have hcoef : 0 < (1 / 4 : ℝ) - 7 * z ^ 2 / 12 := by
    nlinarith [sq_nonneg z]
  have hmain : 3 < X * ((1 / 4 : ℝ) - 7 * z ^ 2 / 12) := by
    have hfloor : 3 < (191 / 10 : ℝ) * ((1 / 4 : ℝ) - 7 * (3 / 10 : ℝ) ^ 2 / 12) := by
      norm_num
    have hzsq : z ^ 2 < (3 / 10 : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hX) hcoef]
  nlinarith

theorem thetaCuspModularUpperProjectiveClockGap_pos
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    0 < thetaCuspModularUpperProjectiveClockGap x := by
  have hmono : StrictMonoOn thetaCuspModularUpperProjectiveClockGap (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact (continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_thetaCuspModularUpperProjectiveClockGap y).continuousAt).continuousOn
    · intro y hy
      have hy' : y ∈ Ioo 0 x := by simpa only [interior_Icc] using hy
      exact deriv_thetaCuspModularUpperProjectiveClockGap_pos hy'.1 (hy'.2.trans hx1)
  have h := hmono (by exact ⟨le_rfl, hx0.le⟩) (by exact ⟨hx0.le, le_rfl⟩) hx0
  simpa using h

theorem thetaCuspModularProjectiveClocks_mem_thinCone
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < (137 / 2000 : ℝ)) :
    (2 / 5 : ℝ) * thetaCuspModularPositiveLambdaClock x <
        thetaCuspModularNormalizedQuasimodularDrift x ∧
      thetaCuspModularNormalizedQuasimodularDrift x <
        (1 / 2 : ℝ) * thetaCuspModularPositiveLambdaClock x := by
  constructor
  · simpa [thetaCuspModularLowerProjectiveClockGap, sub_pos] using
      thetaCuspModularLowerProjectiveClockGap_pos hx0
  · simpa [thetaCuspModularUpperProjectiveClockGap, sub_pos] using
      thetaCuspModularUpperProjectiveClockGap_pos hx0 hx1

end

end RHTower

