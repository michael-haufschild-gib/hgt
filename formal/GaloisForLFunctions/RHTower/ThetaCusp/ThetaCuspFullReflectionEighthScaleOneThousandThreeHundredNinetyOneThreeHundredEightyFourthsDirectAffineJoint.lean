import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsFockFloor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodFourthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsExactAtomLower
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsAffineBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthScaleTwentyNineEighthsDirectAffineJoint

/-!
# Direct-eighth affine joint chamber at scale 1391/384

Independent fourth/sixth rectangles fail at this scale.  The retained dominant-pair eighth
Fock mass supplies a direct moving eighth floor.  Keeping that floor inside the exact nonlinear
compact reserve closes `815/384 ≤ q ≤ 17/8`.
-/

namespace RHTower

noncomputable section

/-- Moving direct logarithmic eighth floor on the scale-`1391/384` chamber. -/
def thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile (q : ℝ) : ℝ :=
  440000 * (q + 3 / 2) ^ (8 : ℕ) * (1 / 52450) *
    (1 - 3 * (q - 815 / 384))

/-- Compact reserve with fourth, sixth, and direct eighth displacements left independent. -/
def thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
    (q e4 e6 e8 : ℝ) : ℝ :=
  thetaCuspFirstAtomEighthNoSixthLossBaseline q +
    e4 * (68 * e4 ^ (2 : ℕ) +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
        204 * thetaCuspFirstAtomFourthProfile q) * e4 +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q) +
    (thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4) * e8 -
    e6 * (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6)

set_option maxHeartbeats 6000000 in
/-- Exact moving fourth/sixth/eighth baseline has strict reserve throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_pos_at_baseline
    {q : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8) :
    0 < thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
      q (969 / 2 - 192 * q)
      ((8016 / 125 : ℝ) * (2605 / 2 - 480 * q))
      (thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 815 / 384
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 384 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
        q (969 / 2 - 192 * q)
        ((8016 / 125 : ℝ) * (2605 / 2 - 480 * q))
        (thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q) := by
    dsimp [thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve,
      thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 815 / 384 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : y ^ (2 : ℕ) ≤ (1 / 384 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hy hyhi 2
    have hy3 : y ^ (3 : ℕ) ≤ (1 / 384 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hy hyhi 3
    have hy4 : y ^ (4 : ℕ) ≤ (1 / 384 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hy hyhi 4
    have hy5 : y ^ (5 : ℕ) ≤ (1 / 384 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hy hyhi 5
    have hy6 : y ^ (6 : ℕ) ≤ (1 / 384 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hy hyhi 6
    have hy7 : y ^ (7 : ℕ) ≤ (1 / 384 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hy hyhi 7
    have hy8 : y ^ (8 : ℕ) ≤ (1 / 384 : ℝ) ^ (8 : ℕ) := pow_le_pow_left₀ hy hyhi 8
    have hy9 : y ^ (9 : ℕ) ≤ (1 / 384 : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ hy hyhi 9
    have hy10 : y ^ (10 : ℕ) ≤ (1 / 384 : ℝ) ^ (10 : ℕ) := pow_le_pow_left₀ hy hyhi 10
    have hy11 : y ^ (11 : ℕ) ≤ (1 / 384 : ℝ) ^ (11 : ℕ) := pow_le_pow_left₀ hy hyhi 11
    have hy12 : y ^ (12 : ℕ) ≤ (1 / 384 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ hy hyhi 12
    have hy13 : y ^ (13 : ℕ) ≤ (1 / 384 : ℝ) ^ (13 : ℕ) := pow_le_pow_left₀ hy hyhi 13
    have hy14 : y ^ (14 : ℕ) ≤ (1 / 384 : ℝ) ^ (14 : ℕ) := pow_le_pow_left₀ hy hyhi 14
    have hy15 : y ^ (15 : ℕ) ≤ (1 / 384 : ℝ) ^ (15 : ℕ) := pow_le_pow_left₀ hy hyhi 15
    have hy16 : y ^ (16 : ℕ) ≤ (1 / 384 : ℝ) ^ (16 : ℕ) := pow_le_pow_left₀ hy hyhi 16
    have hy17 : y ^ (17 : ℕ) ≤ (1 / 384 : ℝ) ^ (17 : ℕ) := pow_le_pow_left₀ hy hyhi 17
    have hy18 : y ^ (18 : ℕ) ≤ (1 / 384 : ℝ) ^ (18 : ℕ) := pow_le_pow_left₀ hy hyhi 18
    have hy19 : y ^ (19 : ℕ) ≤ (1 / 384 : ℝ) ^ (19 : ℕ) := pow_le_pow_left₀ hy hyhi 19
    have hy20 : y ^ (20 : ℕ) ≤ (1 / 384 : ℝ) ^ (20 : ℕ) := pow_le_pow_left₀ hy hyhi 20
    have hy21 : y ^ (21 : ℕ) ≤ (1 / 384 : ℝ) ^ (21 : ℕ) := pow_le_pow_left₀ hy hyhi 21
    have hy22 : y ^ (22 : ℕ) ≤ (1 / 384 : ℝ) ^ (22 : ℕ) := pow_le_pow_left₀ hy hyhi 22
    have hy23 : y ^ (23 : ℕ) ≤ (1 / 384 : ℝ) ^ (23 : ℕ) := pow_le_pow_left₀ hy hyhi 23
    have hy24 : y ^ (24 : ℕ) ≤ (1 / 384 : ℝ) ^ (24 : ℕ) := pow_le_pow_left₀ hy hyhi 24
    have hy25 : 0 ≤ y ^ (25 : ℕ) := by positivity
    norm_num at hyhi hy2 hy3 hy4 hy5 hy6 hy7 hy8 hy9 hy10 hy11 hy12 hy13 hy14
    norm_num at hy15 hy16 hy17 hy18 hy19 hy20 hy21 hy22 hy23 hy24 ⊢
    nlinarith
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 16)

set_option maxHeartbeats 6000000 in
/-- Fourth-direction quadratic coefficient is positive throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale1391Over384_fourthQuadraticCoefficient_pos
    {q : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8) :
    0 < 204 * (969 / 2 - 192 * q) +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
        204 * thetaCuspFirstAtomFourthProfile q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 815 / 384
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 384 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (8 : ℕ) *
      (204 * (969 / 2 - 192 * q) +
        (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
          204 * thetaCuspFirstAtomFourthProfile q)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile]
    field_simp [hqpos.ne']
    rw [show q = 815 / 384 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
    have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
    have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
    have hy5 : y ^ (5 : ℕ) ≤ (1 / 384 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hy hyhi 5
    have hy6 : y ^ (6 : ℕ) ≤ (1 / 384 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hy hyhi 6
    have hy7 : y ^ (7 : ℕ) ≤ (1 / 384 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hy hyhi 7
    have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
    have hy9 : 0 ≤ y ^ (9 : ℕ) := by positivity
    have hy10 : 0 ≤ y ^ (10 : ℕ) := by positivity
    norm_num at hy5 hy6 hy7 ⊢
    nlinarith
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 8)

set_option maxHeartbeats 6000000 in
/-- Fourth-direction constant coefficient is positive throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale1391Over384_fourthConstantCoefficient_pos
    {q : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (_hqhi : q ≤ 17 / 8) :
    let L := 969 / 2 - 192 * q
    let C := 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
      204 * thetaCuspFirstAtomFourthProfile q
    0 < 204 * L ^ (2 : ℕ) + 2 * C * L +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q := by
  dsimp only
  have hqpos : 0 < q := by linarith
  let y := q - 815 / 384
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      (204 * (969 / 2 - 192 * q) ^ (2 : ℕ) +
        2 * (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
          204 * thetaCuspFirstAtomFourthProfile q) * (969 / 2 - 192 * q) +
        thetaCuspFullReflectionEighthCompactFourthCoefficient q) := by
    dsimp [thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 815 / 384 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 16)

set_option maxHeartbeats 6000000 in
/-- Eighth gain coefficient is positive at the moving fourth floor. -/
theorem thetaCuspFirstAtomEighthScale1391Over384_eighthGainCoefficient_pos
    {q : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8) :
    0 < thetaCuspFullReflectionEighthCompactEighthCoefficient q +
      (969 / 2 - 192 * q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 815 / 384
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 384 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (8 : ℕ) *
      (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
        (969 / 2 - 192 * q)) := by
    dsimp [thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile]
    field_simp [hqpos.ne']
    rw [show q = 815 / 384 + y by dsimp only [y]; ring]
    ring_nf
    have hy2 : y ^ (2 : ℕ) ≤ (1 / 384 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hy hyhi 2
    have hy3 : y ^ (3 : ℕ) ≤ (1 / 384 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hy hyhi 3
    have hy4 : y ^ (4 : ℕ) ≤ (1 / 384 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ hy hyhi 4
    have hy5 : y ^ (5 : ℕ) ≤ (1 / 384 : ℝ) ^ (5 : ℕ) := pow_le_pow_left₀ hy hyhi 5
    have hy6 : y ^ (6 : ℕ) ≤ (1 / 384 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ hy hyhi 6
    have hy7 : y ^ (7 : ℕ) ≤ (1 / 384 : ℝ) ^ (7 : ℕ) := pow_le_pow_left₀ hy hyhi 7
    have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
    have hy9 : 0 ≤ y ^ (9 : ℕ) := by positivity
    norm_num at hy2 hy3 hy4 hy5 hy6 hy7 ⊢
    nlinarith
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 8)

set_option maxHeartbeats 6000000 in
/-- Sixth loss coefficient is positive throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale1391Over384_sixthLossCoefficient_pos
    {q : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (_hqhi : q ≤ 17 / 8) :
    0 < thetaCuspFullReflectionEighthCompactSixthCoefficient q := by
  have hqpos : 0 < q := by linarith
  let y := q - 815 / 384
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (6 : ℕ) * thetaCuspFullReflectionEighthCompactSixthCoefficient q := by
    dsimp [thetaCuspFullReflectionEighthCompactSixthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 815 / 384 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 6)

/-- Moving direct eighth floor is positive throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile_pos
    {q : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8) :
    0 < thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q := by
  dsimp only [thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile]
  have hscale : 0 < q + 3 / 2 := by linarith
  have hlinear : 0 < 1 - 3 * (q - 815 / 384) := by linarith
  positivity

/-- Direct compact reserve increases above the moving fourth floor. -/
theorem thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_mono_fourth
    {q e4 e6 e8 : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8)
    (he4 : 969 / 2 - 192 * q ≤ e4) (he8zero : 0 ≤ e8) :
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
        q (969 / 2 - 192 * q) e6 e8 ≤
      thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve q e4 e6 e8 := by
  let a := e4 - (969 / 2 - 192 * q)
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  let L := 969 / 2 - 192 * q
  let C := 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
    204 * thetaCuspFirstAtomFourthProfile q
  let D := thetaCuspFullReflectionEighthCompactFourthCoefficient q
  have hquad : 0 < 204 * L + C := by
    simpa only [L, C] using
      thetaCuspFirstAtomEighthScale1391Over384_fourthQuadraticCoefficient_pos hqlo hqhi
  have hconst : 0 < 204 * L ^ (2 : ℕ) + 2 * C * L + D := by
    simpa only [L, C, D] using
      thetaCuspFirstAtomEighthScale1391Over384_fourthConstantCoefficient_pos hqlo hqhi
  have hbracket : 0 ≤ 68 * a ^ (2 : ℕ) + (204 * L + C) * a +
      (204 * L ^ (2 : ℕ) + 2 * C * L + D) + e8 := by positivity
  have hid :
      thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve q e4 e6 e8 -
          thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve q L e6 e8 =
        a * (68 * a ^ (2 : ℕ) + (204 * L + C) * a +
          (204 * L ^ (2 : ℕ) + 2 * C * L + D) + e8) := by
    dsimp [thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve, a, L, C, D]
    ring
  rw [show 969 / 2 - 192 * q = L by rfl]
  rw [← sub_nonneg, hid]
  positivity

/-- Direct compact reserve decreases toward the moving sixth ceiling. -/
theorem thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_mono_sixth
    {q e6 e8 : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8)
    (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (8016 / 125 : ℝ) * (2605 / 2 - 480 * q)) :
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
        q (969 / 2 - 192 * q)
          ((8016 / 125 : ℝ) * (2605 / 2 - 480 * q)) e8 ≤
      thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
        q (969 / 2 - 192 * q) e6 e8 := by
  let M := (8016 / 125 : ℝ) * (2605 / 2 - 480 * q)
  have hMcore : 0 ≤ 2605 / 2 - 480 * q := by linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hcoeff := thetaCuspFirstAtomEighthScale1391Over384_sixthLossCoefficient_pos hqlo hqhi
  have hgap : 0 ≤ M - e6 := by dsimp only [M]; linarith
  have hfactor : 0 ≤
      thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M := by positivity
  have hprod := mul_nonneg hgap hfactor
  have hid :
      thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
          q (969 / 2 - 192 * q) e6 e8 -
        thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve
          q (969 / 2 - 192 * q) M e8 =
        (M - e6) *
          (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M) := by
    dsimp [thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve]
    ring
  dsimp only [M] at hprod hid ⊢
  linarith

/-- Direct compact reserve increases above the moving eighth floor. -/
theorem thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_mono_eighth
    {q e4 e6 e8 : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8)
    (he4 : 969 / 2 - 192 * q ≤ e4)
    (he8 : thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q ≤ e8) :
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve q e4 e6
        (thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q) ≤
      thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve q e4 e6 e8 := by
  have hbase := thetaCuspFirstAtomEighthScale1391Over384_eighthGainCoefficient_pos hqlo hqhi
  have hcoeff : 0 ≤ thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4 := by
    linarith
  have hgap : 0 ≤ e8 - thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q := by
    linarith
  rw [← sub_nonneg]
  dsimp [thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve]
  nlinarith [mul_nonneg hcoeff hgap]

/-- Exact direct-eighth joint chamber for arbitrary admissible fourth, sixth, and eighth jets. -/
theorem thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_pos
    {q e4 e6 e8 : ℝ} (hqlo : (815 / 384 : ℝ) ≤ q) (hqhi : q ≤ 17 / 8)
    (he4 : 969 / 2 - 192 * q ≤ e4) (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (8016 / 125 : ℝ) * (2605 / 2 - 480 * q))
    (he8 : thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q ≤ e8) :
    0 < thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve q e4 e6 e8 := by
  have hbase :=
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_pos_at_baseline hqlo hqhi
  have hsix :=
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_mono_sixth
      hqlo hqhi he6zero he6hi
        (e8 := thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q)
  have hprofileNonneg :=
    (thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile_pos hqlo hqhi).le
  have hfourth :=
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_mono_fourth
      hqlo hqhi he4 hprofileNonneg (e6 := e6)
  have heighth :=
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_mono_eighth
      hqlo hqhi he4 he8 (e6 := e6)
  linarith

/-- Physical compact reserve is positive on `1391/384 ≤ A ≤ 29/8`. -/
theorem thetaCuspFullReflectionEighthCompactReserve_pos_of_scale1391Over384_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (1391 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 29 / 8) :
    0 < thetaCuspFullReflectionEighthCompactReserve x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  have hAq : A = q + 3 / 2 := by
    dsimp only [A, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hqlo : (815 / 384 : ℝ) ≤ q := by
    have h := hAlo
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have hqhi : q ≤ (17 / 8 : ℝ) := by
    have h := hAhi
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have he4 : 969 / 2 - 192 * q ≤ e4 := by
    have h := fourth1391Over384AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
      hx hAlo hAhi
    simpa only [q, e4] using h.le
  have he6zero : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he6hi : e6 ≤ (8016 / 125 : ℝ) * (2605 / 2 - 480 * q) := by
    have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale1391Over384_affine_weight
      hx hAlo hAhi
    simpa only [q, e6] using h.le
  have hexp := thetaCuspLikelihoodFourthScale1391Over384_expAffine_lt_exp_neg_three_mul
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hexp' : (1 / 52450 : ℝ) * (1 - 3 * (A - 1391 / 384)) <
      Real.exp (-(3 * A)) := by
    simpa only [A, neg_mul] using hexp
  have hApos : 0 < A := by dsimp only [A] at hAlo ⊢; linarith
  have heighthFloor :=
    fourHundredFortyThousand_mul_pow_eight_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetEight_of_1391Over384_le
      hx hAlo
  have he8 : thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q ≤ e8 := by
    have hlower :
        thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q <
          440000 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
      have hprofileEq :
          thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q =
            (440000 * A ^ (8 : ℕ)) *
              ((1 / 52450 : ℝ) * (1 - 3 * (A - 1391 / 384))) := by
        dsimp only [thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile]
        rw [hAq]
        ring
      calc
        thetaCuspFirstAtomEighthScale1391Over384DirectEighthProfile q =
            (440000 * A ^ (8 : ℕ)) *
              ((1 / 52450 : ℝ) * (1 - 3 * (A - 1391 / 384))) := hprofileEq
        _ < (440000 * A ^ (8 : ℕ)) * Real.exp (-(3 * A)) :=
          mul_lt_mul_of_pos_left hexp' (by positivity)
        _ = 440000 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by ring
    have hfloor : 440000 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) < e8 := by
      simpa only [A, e8] using heighthFloor
    exact (hlower.trans hfloor).le
  have hjoint := thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve_pos
    hqlo hqhi he4 he6zero he6hi he8
  simpa [thetaCuspFullReflectionEighthCompactReserve,
    thetaCuspFirstAtomEighthScale1391Over384DirectJointReserve, q, e4, e6, e8] using hjoint

/-- Native D1 is positive on `1391/384 ≤ A ≤ 29/8`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_scale1391Over384_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (1391 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 29 / 8) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hreserve := thetaCuspFullReflectionEighthCompactReserve_pos_of_scale1391Over384_mem
    hx hAlo hAhi
  have hlower := thetaCuspFullReflectionEighthCompactReserve_le_hankelCurvature hx
  linarith

/-- Native D1 is strict whenever first-atom weight is at least `815/384`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_815Over384_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (815 / 384 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqhi : thetaCuspBornWittenWeight 1 x ≤ (17 / 8 : ℝ)
  · have hscale : thetaCuspSingleAtomReflectionScale 1 x =
        thetaCuspBornWittenWeight 1 x + 3 / 2 := by
      dsimp only [thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAlo : (1391 / 384 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]
      linarith
    have hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (29 / 8 : ℝ) := by
      rw [hscale]
      linarith
    exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_scale1391Over384_mem
      hx hAlo hAhi
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_17Over8_le_weight
      hx (le_of_not_ge hqhi)

/-- Exact Taylor certificate placing `x = 143/2000` above scale `1391/384`. -/
theorem oneThousandThreeHundredNinetyOneThreeHundredEightyFourths_lt_pi_mul_exp_oneHundredFortyThreeThousandths :
    (1391 / 384 : ℝ) < Real.pi * Real.exp (143 / 1000 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 143 / 1000) 8
  have hp := Real.pi_gt_d20
  calc
    (1391 / 384 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (∑ k ∈ Finset.range 8, (143 / 1000 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi * Real.exp (143 / 1000 : ℝ) := by gcongr

/-- Native D1 is strict on the improved source half-line `x ≥ 143/2000`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_oneHundredFortyThreeTwoThousandths_le
    {x : ℝ} (hx : (143 / 2000 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (143 / 1000 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (1391 / 384 : ℝ) < Real.pi * Real.exp (2 * x) :=
    oneThousandThreeHundredNinetyOneThreeHundredEightyFourths_lt_pi_mul_exp_oneHundredFortyThreeThousandths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (815 / 384 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_815Over384_le_weight
    hx0 hqBound

end

end RHTower
