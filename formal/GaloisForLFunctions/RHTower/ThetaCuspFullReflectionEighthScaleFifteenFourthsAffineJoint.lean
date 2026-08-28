import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleFifteenFourthsAffineLower
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleFifteenFourthsAffineBound
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleTwentyThreeSixthsJoint

/-!
# Affine fourth/sixth joint chamber at scale fifteen fourths

The moving source bounds
`292 - 108q < J₄` and `J₆ < (1656/25)(968 - 324q)` are inserted simultaneously into the
exact sixth-spectral eighth-reflection reserve.  After shifting `q = 9/4 + y`, its cleared
baseline has strictly positive coefficients.  Monotonicity in both live jets transfers the
certificate to the physical source and extends native D1 from `x ≥ 1/10` to `x ≥ 9/100`.
-/

namespace RHTower

noncomputable section

set_option maxHeartbeats 6000000 in
/-- The exact moving fourth/sixth baseline leaves a strict reserve throughout the new chamber. -/
theorem thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_pos_at_baseline
    {q : ℝ} (hqlo : (9 / 4 : ℝ) ≤ q) (hqhi : q ≤ 7 / 3) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
      q (292 - 108 * q) ((1656 / 25 : ℝ) * (968 - 324 * q)) := by
  have hqpos : 0 < q := by linarith
  let y := q - 9 / 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 16 *
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (292 - 108 * q) ((1656 / 25 : ℝ) * (968 - 324 * q)) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 9 / 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

set_option maxHeartbeats 6000000 in
/-- The joint reserve is increasing above its moving fourth-jet floor. -/
theorem thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_mono_fourth
    {q e4 e6 : ℝ} (hqlo : (9 / 4 : ℝ) ≤ q) (hqhi : q ≤ 7 / 3)
    (he4 : 292 - 108 * q ≤ e4) (he6zero : 0 ≤ e6) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (292 - 108 * q) e6 ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hqpos : 0 < q := by linarith
  let y := q - 9 / 4
  let a := e4 - (292 - 108 * q)
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  have hmul : 0 ≤ q ^ 16 *
      (thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 -
        thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
          q (292 - 108 * q) e6) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 9 / 4 + y by dsimp only [y]; ring,
      show e4 = 49 - 108 * y + a by dsimp only [a, y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

set_option maxHeartbeats 6000000 in
/-- The factored sixth-loss coefficient remains positive along the moving baseline. -/
theorem thetaCuspFirstAtomEighthScaleFifteenFourthsAffine_sixthLossCoefficient_pos
    {q : ℝ} (hqlo : (9 / 4 : ℝ) ≤ q) (hqhi : q ≤ 7 / 3) :
    0 < thetaCuspFullReflectionEighthCompactSixthCoefficient q +
        (1656 / 25 : ℝ) * (968 - 324 * q) -
      (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
          (292 - 108 * q)) * (1 / 69) * (q + 3 / 2) ^ 2 := by
  have hqpos : 0 < q := by linarith
  let y := q - 9 / 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 12 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 12 *
      (thetaCuspFullReflectionEighthCompactSixthCoefficient q +
          (1656 / 25 : ℝ) * (968 - 324 * q) -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
            (292 - 108 * q)) * (1 / 69) * (q + 3 / 2) ^ 2) := by
    dsimp [thetaCuspFullReflectionEighthCompactSixthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 9 / 4 + y by dsimp only [y]; ring]
    ring_nf
    have hc : 0 < 5627256000 - 640000 * y := by linarith
    have hlast : 0 ≤ y ^ 15 * 5627256000 - y ^ 16 * 640000 := by
      rw [show y ^ 15 * 5627256000 - y ^ 16 * 640000 =
          y ^ 15 * (5627256000 - 640000 * y) by ring]
      positivity
    have hprefix : 0 <
        90634584092675911320825 / 8388608 +
          y * (251572417167371235576975 / 4194304) +
          y ^ 2 * (10198176309849620311875 / 65536) +
          y ^ 3 * (65676191572604890773225 / 262144) +
          y ^ 4 * (9181657563033976077825 / 32768) +
          y ^ 5 * (3781520775994315816575 / 16384) +
          y ^ 6 * (148242294518780987325 / 1024) +
          y ^ 7 * (72146347799162360625 / 1024) +
          y ^ 8 * (3435280709453417025 / 128) +
          y ^ 9 * (512250598701800325 / 64) +
          y ^ 10 * (3706976561110425 / 2) +
          y ^ 11 * (1308645674687475 / 4) +
          y ^ 12 * 42569960388750 +
          y ^ 13 * 3849070590900 +
          y ^ 14 * 215737134400 := by
      positivity
    nlinarith
  nlinarith [pow_pos hqpos 12]

/-- The reserve decreases toward the moving sixth-jet ceiling. -/
theorem thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_mono_sixth
    {q e6 : ℝ} (hqlo : (9 / 4 : ℝ) ≤ q) (hqhi : q ≤ 7 / 3)
    (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (1656 / 25 : ℝ) * (968 - 324 * q)) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (292 - 108 * q) ((1656 / 25 : ℝ) * (968 - 324 * q)) ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (292 - 108 * q) e6 := by
  let M := (1656 / 25 : ℝ) * (968 - 324 * q)
  let L := 292 - 108 * q
  have hcoeff :=
    thetaCuspFirstAtomEighthScaleFifteenFourthsAffine_sixthLossCoefficient_pos
      hqlo hqhi
  have hgap : 0 ≤ M - e6 := by dsimp only [M]; linarith
  have hfactor : 0 ≤
      thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q + L) *
          (1 / 69) * (q + 3 / 2) ^ 2 := by
    dsimp only [M, L] at hcoeff ⊢
    linarith
  have hprod := mul_nonneg hgap hfactor
  have hid :
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L e6 -
          thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L M =
        (M - e6) *
          (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M -
            (thetaCuspFullReflectionEighthCompactEighthCoefficient q + L) *
              (1 / 69) * (q + 3 / 2) ^ 2) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve]
    ring
  dsimp only [L, M] at hprod hid ⊢
  linarith

/-- Exact joint chamber for arbitrary live fourth and sixth jets. -/
theorem thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_pos
    {q e4 e6 : ℝ} (hqlo : (9 / 4 : ℝ) ≤ q) (hqhi : q ≤ 7 / 3)
    (he4 : 292 - 108 * q ≤ e4) (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (1656 / 25 : ℝ) * (968 - 324 * q)) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hbase :=
    thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_pos_at_baseline
      hqlo hqhi
  have hsix :=
    thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_mono_sixth
      hqlo hqhi he6zero he6hi
  have hfourth :=
    thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_mono_fourth
      hqlo hqhi he4 he6zero
  linarith

/-- The physical sixth-spectral reserve is positive on `15/4 ≤ A ≤ 23/6`. -/
theorem thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_fifteenFourths_scale_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 23 / 6) :
    0 < thetaCuspFullReflectionEighthSixthSpectralReserve x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  have hAq : A = q + 3 / 2 := by
    dsimp only [A, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hqlo : (9 / 4 : ℝ) ≤ q := by
    have h := hAlo
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have hqhi : q ≤ (7 / 3 : ℝ) := by
    have h := hAhi
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have he4 : 292 - 108 * q ≤ e4 := by
    have h := fourthAffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
      hx hAlo hAhi
    simpa only [q, e4] using h.le
  have he6zero : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he6hi : e6 ≤ (1656 / 25 : ℝ) * (968 - 324 * q) := by
    have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_affine_weight_of_scale_mem
      hx hAlo hAhi
    simpa only [q, e6] using h.le
  have hjoint := thetaCuspFirstAtomEighthScaleFifteenFourthsAffineJointReserve_pos
    hqlo hqhi he4 he6zero he6hi
  dsimp only [thetaCuspFullReflectionEighthSixthSpectralReserve]
  dsimp only [q, A, e4, e6] at hjoint ⊢
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    simpa only [A, q] using hAq
  rw [hscale]
  exact hjoint

/-- Native D1 is strict whenever the first-atom weight is at least `9/4`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineFourths_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (9 / 4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqhi : thetaCuspBornWittenWeight 1 x ≤ (7 / 3 : ℝ)
  · have hscale : thetaCuspSingleAtomReflectionScale 1 x =
        thetaCuspBornWittenWeight 1 x + 3 / 2 := by
      dsimp only [thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAlo : (15 / 4 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]
      linarith
    have hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (23 / 6 : ℝ) := by
      rw [hscale]
      linarith
    exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_sixthSpectralReserve_pos hx
      (thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_fifteenFourths_scale_mem
        hx hAlo hAhi)
  · exact
      thetaCuspFullReflectionEighthHankelCurvature_pos_of_sevenThirds_le_weight_of_jointReserve
        hx (le_of_not_ge hqhi)

/-- Exact Taylor certificate placing `x = 9/100` above scale `15/4`. -/
theorem fifteenFourths_lt_pi_mul_exp_nineFiftieths :
    (15 / 4 : ℝ) < Real.pi * Real.exp (9 / 50 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 9 / 50) 8
  have hp := Real.pi_gt_d20
  calc
    (15 / 4 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (∑ k ∈ Finset.range 8, (9 / 50 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi * Real.exp (9 / 50 : ℝ) := by gcongr

/-- Native D1 is strict on the improved source half-line `x ≥ 9/100`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineHundredths_le
    {x : ℝ} (hx : (9 / 100 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (9 / 50 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (15 / 4 : ℝ) < Real.pi * Real.exp (2 * x) :=
    fifteenFourths_lt_pi_mul_exp_nineFiftieths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (9 / 4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineFourths_le_weight
    hx0 hqBound

end
end RHTower
