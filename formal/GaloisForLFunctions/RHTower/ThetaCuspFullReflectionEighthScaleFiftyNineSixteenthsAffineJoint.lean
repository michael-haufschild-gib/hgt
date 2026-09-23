import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleFiftyNineSixteenthsAffineLower
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleFiftyNineSixteenthsAffineBound
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleEightyNineTwentyFourthsAffineJoint

/-!
# Affine fourth/sixth joint chamber at scale 59/16

The moving bounds `796 - 336q < J₄` and `J₆ < (1656/25)(1196 - 432q)` are
inserted into the exact sixth-spectral eighth-reflection reserve. On
`35/16 ≤ q ≤ 53/24`, the coupled reserve remains positive. Native D1 consequently holds for
`x ≥ 81/1000`.
-/

namespace RHTower

noncomputable section

set_option maxHeartbeats 6000000 in
/-- Exact moving fourth/sixth baseline leaves strict reserve throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_pos_at_baseline
    {q : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (hqhi : q ≤ 53 / 24) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
      q (796 - 336 * q) ((1656 / 25 : ℝ) * (1196 - 432 * q)) := by
  have hqpos : 0 < q := by linarith
  let y := q - 35 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 48 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (796 - 336 * q) ((1656 / 25 : ℝ) * (1196 - 432 * q)) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 35 / 16 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : y ^ (2 : ℕ) ≤ (1 / 48 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hy hyhi 2
    have hy3 : y ^ (3 : ℕ) ≤ (1 / 48 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hy hyhi 3
    have hy4 : y ^ (4 : ℕ) ≤ (1 / 48 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hy hyhi 4
    have hy5 : y ^ (5 : ℕ) ≤ (1 / 48 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hy hyhi 5
    have hy6 : y ^ (6 : ℕ) ≤ (1 / 48 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hy hyhi 6
    have hy7 : y ^ (7 : ℕ) ≤ (1 / 48 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hy hyhi 7
    have hy8 : y ^ (8 : ℕ) ≤ (1 / 48 : ℝ) ^ (8 : ℕ) := pow_le_pow_left₀ hy hyhi 8
    have hy9 : y ^ (9 : ℕ) ≤ (1 / 48 : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ hy hyhi 9
    have hy10 : y ^ (10 : ℕ) ≤ (1 / 48 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ hy hyhi 10
    have hy11 : y ^ (11 : ℕ) ≤ (1 / 48 : ℝ) ^ (11 : ℕ) := pow_le_pow_left₀ hy hyhi 11
    have hy12 : y ^ (12 : ℕ) ≤ (1 / 48 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ hy hyhi 12
    have hy13 : y ^ (13 : ℕ) ≤ (1 / 48 : ℝ) ^ (13 : ℕ) := pow_le_pow_left₀ hy hyhi 13
    have hy14 : y ^ (14 : ℕ) ≤ (1 / 48 : ℝ) ^ (14 : ℕ) := pow_le_pow_left₀ hy hyhi 14
    have hy15 : y ^ (15 : ℕ) ≤ (1 / 48 : ℝ) ^ (15 : ℕ) := pow_le_pow_left₀ hy hyhi 15
    have hy16 : y ^ (16 : ℕ) ≤ (1 / 48 : ℝ) ^ (16 : ℕ) := pow_le_pow_left₀ hy hyhi 16
    have hy17 : y ^ (17 : ℕ) ≤ (1 / 48 : ℝ) ^ (17 : ℕ) := pow_le_pow_left₀ hy hyhi 17
    have hy18 : y ^ (18 : ℕ) ≤ (1 / 48 : ℝ) ^ (18 : ℕ) := pow_le_pow_left₀ hy hyhi 18
    have hy19 : y ^ (19 : ℕ) ≤ (1 / 48 : ℝ) ^ (19 : ℕ) := pow_le_pow_left₀ hy hyhi 19
    have hy20 : y ^ (20 : ℕ) ≤ (1 / 48 : ℝ) ^ (20 : ℕ) := pow_le_pow_left₀ hy hyhi 20
    have hy21 : 0 ≤ y ^ (21 : ℕ) := by positivity
    have hy22 : 0 ≤ y ^ (22 : ℕ) := by positivity
    norm_num at hyhi hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9 hy10 hy11 hy12 hy13 hy14
    norm_num at hy15 hy16 hy17 hy18 hy19 hy20 ⊢
    nlinarith
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 16)

set_option maxHeartbeats 6000000 in
/-- The quadratic coefficient in the fourth direction is positive on the chamber. -/
theorem thetaCuspFirstAtomEighthScale59Over16Affine_fourthQuadraticCoefficient_pos
    {q : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (hqhi : q ≤ 53 / 24) :
    0 < 204 * (796 - 336 * q) +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
        204 * thetaCuspFirstAtomFourthProfile q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 35 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 48 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (8 : ℕ) *
      (204 * (796 - 336 * q) +
        (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
          204 * thetaCuspFirstAtomFourthProfile q)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile]
    field_simp [hqpos.ne']
    rw [show q = 35 / 16 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
    have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
    have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
    have hy5 : y ^ (5 : ℕ) ≤ (1 / 48 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hy hyhi 5
    have hy6 : y ^ (6 : ℕ) ≤ (1 / 48 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hy hyhi 6
    have hy7 : y ^ (7 : ℕ) ≤ (1 / 48 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hy hyhi 7
    have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
    have hy9 : 0 ≤ y ^ (9 : ℕ) := by positivity
    have hy10 : 0 ≤ y ^ (10 : ℕ) := by positivity
    norm_num at hy5 hy6 hy7 ⊢
    nlinarith
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 8)

set_option maxHeartbeats 6000000 in
/-- The constant coefficient in the fourth direction is positive on the chamber. -/
theorem thetaCuspFirstAtomEighthScale59Over16Affine_fourthConstantCoefficient_pos
    {q : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (_hqhi : q ≤ 53 / 24) :
    let L := 796 - 336 * q
    let C := 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
      204 * thetaCuspFirstAtomFourthProfile q
    0 < 204 * L ^ (2 : ℕ) + 2 * C * L +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q := by
  dsimp only
  have hqpos : 0 < q := by linarith
  let y := q - 35 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      (204 * (796 - 336 * q) ^ (2 : ℕ) +
        2 * (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
          204 * thetaCuspFirstAtomFourthProfile q) * (796 - 336 * q) +
        thetaCuspFullReflectionEighthCompactFourthCoefficient q) := by
    dsimp [thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 35 / 16 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 16)

/-- Joint reserve is increasing above the moving fourth-jet floor. -/
theorem thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_mono_fourth
    {q e4 e6 : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (hqhi : q ≤ 53 / 24)
    (he4 : 796 - 336 * q ≤ e4) (he6zero : 0 ≤ e6) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (796 - 336 * q) e6 ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  let a := e4 - (796 - 336 * q)
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  let L := 796 - 336 * q
  let C := 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
    204 * thetaCuspFirstAtomFourthProfile q
  let D := thetaCuspFullReflectionEighthCompactFourthCoefficient q
  let K := (1 / 69 : ℝ) * (q + 3 / 2) ^ (2 : ℕ)
  have hquad : 0 < 204 * L + C := by
    simpa only [L, C] using
      thetaCuspFirstAtomEighthScale59Over16Affine_fourthQuadraticCoefficient_pos hqlo hqhi
  have hconst : 0 < 204 * L ^ (2 : ℕ) + 2 * C * L + D := by
    simpa only [L, C, D] using
      thetaCuspFirstAtomEighthScale59Over16Affine_fourthConstantCoefficient_pos hqlo hqhi
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbracket : 0 ≤ 68 * a ^ (2 : ℕ) + (204 * L + C) * a +
      (204 * L ^ (2 : ℕ) + 2 * C * L + D) + e6 * K := by positivity
  have hid :
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 -
          thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L e6 =
        a * (68 * a ^ (2 : ℕ) + (204 * L + C) * a +
          (204 * L ^ (2 : ℕ) + 2 * C * L + D) + e6 * K) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve,
      a, L, C, D, K]
    ring
  rw [show 796 - 336 * q = L by rfl]
  rw [← sub_nonneg]
  rw [hid]
  positivity

set_option maxHeartbeats 6000000 in
/-- Factored sixth-loss coefficient remains positive along the moving baseline. -/
theorem thetaCuspFirstAtomEighthScale59Over16Affine_sixthLossCoefficient_pos
    {q : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (hqhi : q ≤ 53 / 24) :
    0 < thetaCuspFullReflectionEighthCompactSixthCoefficient q +
        (1656 / 25 : ℝ) * (1196 - 432 * q) -
      (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
          (796 - 336 * q)) * (1 / 69) * (q + 3 / 2) ^ (2 : ℕ) := by
  have hqpos : 0 < q := by linarith
  let y := q - 35 / 16
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 48 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (12 : ℕ) *
      (thetaCuspFullReflectionEighthCompactSixthCoefficient q +
          (1656 / 25 : ℝ) * (1196 - 432 * q) -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
            (796 - 336 * q)) * (1 / 69) * (q + 3 / 2) ^ (2 : ℕ)) := by
    dsimp [thetaCuspFullReflectionEighthCompactSixthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 35 / 16 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
    have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
    have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
    have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
    have hy6 : 0 ≤ y ^ (6 : ℕ) := by positivity
    have hy7 : 0 ≤ y ^ (7 : ℕ) := by positivity
    have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
    have hy9 : 0 ≤ y ^ (9 : ℕ) := by positivity
    have hy10 : 0 ≤ y ^ (10 : ℕ) := by positivity
    have hy11 : 0 ≤ y ^ (11 : ℕ) := by positivity
    have hy12 : 0 ≤ y ^ (12 : ℕ) := by positivity
    have hy13 : 0 ≤ y ^ (13 : ℕ) := by positivity
    have hy14 : 0 ≤ y ^ (14 : ℕ) := by positivity
    have hpair : 0 ≤ y ^ (15 : ℕ) * (5630176000 : ℝ) - y ^ (16 : ℕ) * 640000 := by
      have hc : 0 ≤ (5630176000 : ℝ) - 640000 * y := by linarith
      rw [show y ^ (15 : ℕ) * (5630176000 : ℝ) - y ^ (16 : ℕ) * 640000 =
          y ^ (15 : ℕ) * (5630176000 - 640000 * y) by ring]
      positivity
    nlinarith
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 12)

/-- Reserve decreases toward the moving sixth-jet ceiling. -/
theorem thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_mono_sixth
    {q e6 : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (hqhi : q ≤ 53 / 24)
    (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (1656 / 25 : ℝ) * (1196 - 432 * q)) :
    thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (796 - 336 * q) ((1656 / 25 : ℝ) * (1196 - 432 * q)) ≤
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve
        q (796 - 336 * q) e6 := by
  let M := (1656 / 25 : ℝ) * (1196 - 432 * q)
  let L := 796 - 336 * q
  have hcoeff := thetaCuspFirstAtomEighthScale59Over16Affine_sixthLossCoefficient_pos
    hqlo hqhi
  have hgap : 0 ≤ M - e6 := by dsimp only [M]; linarith
  have hfactor : 0 ≤
      thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M -
        (thetaCuspFullReflectionEighthCompactEighthCoefficient q + L) *
          (1 / 69) * (q + 3 / 2) ^ (2 : ℕ) := by
    dsimp only [M, L] at hcoeff ⊢
    linarith
  have hprod := mul_nonneg hgap hfactor
  have hid :
      thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L e6 -
          thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q L M =
        (M - e6) *
          (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M -
            (thetaCuspFullReflectionEighthCompactEighthCoefficient q + L) *
              (1 / 69) * (q + 3 / 2) ^ (2 : ℕ)) := by
    dsimp [thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve]
    ring
  dsimp only [L, M] at hprod hid ⊢
  linarith

/-- Exact joint chamber for arbitrary physical fourth and sixth jets. -/
theorem thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_pos
    {q e4 e6 : ℝ} (hqlo : (35 / 16 : ℝ) ≤ q) (hqhi : q ≤ 53 / 24)
    (he4 : 796 - 336 * q ≤ e4) (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (1656 / 25 : ℝ) * (1196 - 432 * q)) :
    0 < thetaCuspFirstAtomEighthScaleTwentyThreeSixthsJointReserve q e4 e6 := by
  have hbase := thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_pos_at_baseline
    hqlo hqhi
  have hsix := thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_mono_sixth
    hqlo hqhi he6zero he6hi
  have hfourth := thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_mono_fourth
    hqlo hqhi he4 he6zero
  linarith

/-- Physical sixth-spectral reserve is positive on `59/16 ≤ A ≤ 89/24`. -/
theorem thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_scale59Over16_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 89 / 24) :
    0 < thetaCuspFullReflectionEighthSixthSpectralReserve x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  have hAq : A = q + 3 / 2 := by
    dsimp only [A, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hqlo : (35 / 16 : ℝ) ≤ q := by
    have h := hAlo
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have hqhi : q ≤ (53 / 24 : ℝ) := by
    have h := hAhi
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have he4 : 796 - 336 * q ≤ e4 := by
    have h := fourth59Over16AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
      hx hAlo hAhi
    simpa only [q, e4] using h.le
  have he6zero : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he6hi : e6 ≤ (1656 / 25 : ℝ) * (1196 - 432 * q) := by
    have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale59Over16_affine_weight
      hx hAlo hAhi
    simpa only [q, e6] using h.le
  have hjoint := thetaCuspFirstAtomEighthScale59Over16AffineJointReserve_pos
    hqlo hqhi he4 he6zero he6hi
  dsimp only [thetaCuspFullReflectionEighthSixthSpectralReserve]
  dsimp only [q, A, e4, e6] at hjoint ⊢
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    simpa only [A, q] using hAq
  rw [hscale]
  exact hjoint

/-- Native D1 is strict whenever first-atom weight is at least `35/16`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_35Over16_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (35 / 16 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqhi : thetaCuspBornWittenWeight 1 x ≤ (53 / 24 : ℝ)
  · have hscale : thetaCuspSingleAtomReflectionScale 1 x =
        thetaCuspBornWittenWeight 1 x + 3 / 2 := by
      dsimp only [thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAlo : (59 / 16 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]
      linarith
    have hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (89 / 24 : ℝ) := by
      rw [hscale]
      linarith
    exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_sixthSpectralReserve_pos hx
      (thetaCuspFullReflectionEighthSixthSpectralReserve_pos_of_scale59Over16_mem
        hx hAlo hAhi)
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_53Over24_le_weight
      hx (le_of_not_ge hqhi)

/-- Exact Taylor certificate placing `x = 81/1000` above scale `59/16`. -/
theorem fiftyNineSixteenths_lt_pi_mul_exp_eightyOneFiveHundredths :
    (59 / 16 : ℝ) < Real.pi * Real.exp (81 / 500 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 81 / 500) 8
  have hp := Real.pi_gt_d20
  calc
    (59 / 16 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (∑ k ∈ Finset.range 8, (81 / 500 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi * Real.exp (81 / 500 : ℝ) := by gcongr

/-- Native D1 is strict on the improved source half-line `x ≥ 81/1000`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_eightyOneThousandths_le
    {x : ℝ} (hx : (81 / 1000 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (81 / 500 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (59 / 16 : ℝ) < Real.pi * Real.exp (2 * x) :=
    fiftyNineSixteenths_lt_pi_mul_exp_eightyOneFiveHundredths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (35 / 16 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_35Over16_le_weight
    hx0 hqBound

end
end RHTower
