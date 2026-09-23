import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthScaleSixHundredNinetyFiveOneHundredNinetySecondsFockFloor
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodFourthScaleSixHundredNinetyFiveOneHundredNinetySecondsExactAtomLower
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleSixHundredNinetyFiveOneHundredNinetySecondsAffineBound
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsDirectAffineJoint

/-!
# Direct-eighth affine joint chamber at scale 695/192

The scale-local response estimate cools the higher-even Fock loss from `1300/3` to
`13/2`.  Together with the sharpened stable-sixth tail, this opens the adjacent
dyadic chamber `407/192 ≤ q ≤ 815/384`.
-/

namespace RHTower

noncomputable section

/-- Moving direct logarithmic eighth floor on the scale-`695/192` chamber. -/
def thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile (q : ℝ) : ℝ :=
  550000 * (q + 3 / 2) ^ (8 : ℕ) * (1 / 52050) *
    (1 - 3 * (q - 407 / 192))

/-- Compact reserve with fourth, sixth, and direct eighth displacements independent. -/
def thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
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
theorem thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_pos_at_baseline
    {q : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384) :
    0 < thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
      q (969 / 2 - 192 * q)
      ((8016 / 125 : ℝ) * (6512 / 5 - 480 * q))
      (thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 407 / 192
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 384 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
        q (969 / 2 - 192 * q)
        ((8016 / 125 : ℝ) * (6512 / 5 - 480 * q))
        (thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q) := by
    dsimp [thetaCuspFirstAtomEighthScale695Over192DirectJointReserve,
      thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile,
      thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile,
      thetaCuspFullReflectionEighthCompactFourthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFullReflectionEighthCompactSixthCoefficient]
    field_simp [hqpos.ne']
    rw [show q = 407 / 192 + y by dsimp only [y]; ring]
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
theorem thetaCuspFirstAtomEighthScale695Over192_fourthQuadraticCoefficient_pos
    {q : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384) :
    0 < 204 * (969 / 2 - 192 * q) +
      (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
        204 * thetaCuspFirstAtomFourthProfile q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 407 / 192
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 384 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (8 : ℕ) *
      (204 * (969 / 2 - 192 * q) +
        (304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
          204 * thetaCuspFirstAtomFourthProfile q)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile]
    field_simp [hqpos.ne']
    rw [show q = 407 / 192 + y by dsimp only [y]; ring]
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
theorem thetaCuspFirstAtomEighthScale695Over192_fourthConstantCoefficient_pos
    {q : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (_hqhi : q ≤ 815 / 384) :
    let L := 969 / 2 - 192 * q
    let C := 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
      204 * thetaCuspFirstAtomFourthProfile q
    0 < 204 * L ^ (2 : ℕ) + 2 * C * L +
      thetaCuspFullReflectionEighthCompactFourthCoefficient q := by
  dsimp only
  have hqpos : 0 < q := by linarith
  let y := q - 407 / 192
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
    rw [show q = 407 / 192 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 16)

set_option maxHeartbeats 6000000 in
/-- Eighth gain coefficient is positive at the moving fourth floor. -/
theorem thetaCuspFirstAtomEighthScale695Over192_eighthGainCoefficient_pos
    {q : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384) :
    0 < thetaCuspFullReflectionEighthCompactEighthCoefficient q +
      (969 / 2 - 192 * q) := by
  have hqpos : 0 < q := by linarith
  let y := q - 407 / 192
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyhi : y ≤ 1 / 384 := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (8 : ℕ) *
      (thetaCuspFullReflectionEighthCompactEighthCoefficient q +
        (969 / 2 - 192 * q)) := by
    dsimp [thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile]
    field_simp [hqpos.ne']
    rw [show q = 407 / 192 + y by dsimp only [y]; ring]
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
theorem thetaCuspFirstAtomEighthScale695Over192_sixthLossCoefficient_pos
    {q : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (_hqhi : q ≤ 815 / 384) :
    0 < thetaCuspFullReflectionEighthCompactSixthCoefficient q := by
  have hqpos : 0 < q := by linarith
  let y := q - 407 / 192
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (6 : ℕ) * thetaCuspFullReflectionEighthCompactSixthCoefficient q := by
    dsimp [thetaCuspFullReflectionEighthCompactSixthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 407 / 192 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  exact pos_of_mul_pos_right hmul (pow_nonneg hqpos.le 6)

/-- Moving direct eighth floor is positive throughout the chamber. -/
theorem thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile_pos
    {q : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384) :
    0 < thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q := by
  dsimp only [thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile]
  have hscale : 0 < q + 3 / 2 := by linarith
  have hlinear : 0 < 1 - 3 * (q - 407 / 192) := by linarith
  positivity

/-- Direct compact reserve increases above the moving fourth floor. -/
theorem thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_mono_fourth
    {q e4 e6 e8 : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384)
    (he4 : 969 / 2 - 192 * q ≤ e4) (he8zero : 0 ≤ e8) :
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
        q (969 / 2 - 192 * q) e6 e8 ≤
      thetaCuspFirstAtomEighthScale695Over192DirectJointReserve q e4 e6 e8 := by
  let a := e4 - (969 / 2 - 192 * q)
  have ha : 0 ≤ a := by dsimp only [a]; linarith
  let L := 969 / 2 - 192 * q
  let C := 304 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
    204 * thetaCuspFirstAtomFourthProfile q
  let D := thetaCuspFullReflectionEighthCompactFourthCoefficient q
  have hquad : 0 < 204 * L + C := by
    simpa only [L, C] using
      thetaCuspFirstAtomEighthScale695Over192_fourthQuadraticCoefficient_pos hqlo hqhi
  have hconst : 0 < 204 * L ^ (2 : ℕ) + 2 * C * L + D := by
    simpa only [L, C, D] using
      thetaCuspFirstAtomEighthScale695Over192_fourthConstantCoefficient_pos hqlo hqhi
  have hbracket : 0 ≤ 68 * a ^ (2 : ℕ) + (204 * L + C) * a +
      (204 * L ^ (2 : ℕ) + 2 * C * L + D) + e8 := by positivity
  have hid :
      thetaCuspFirstAtomEighthScale695Over192DirectJointReserve q e4 e6 e8 -
          thetaCuspFirstAtomEighthScale695Over192DirectJointReserve q L e6 e8 =
        a * (68 * a ^ (2 : ℕ) + (204 * L + C) * a +
          (204 * L ^ (2 : ℕ) + 2 * C * L + D) + e8) := by
    dsimp [thetaCuspFirstAtomEighthScale695Over192DirectJointReserve, a, L, C, D]
    ring
  rw [show 969 / 2 - 192 * q = L by rfl]
  rw [← sub_nonneg, hid]
  positivity

/-- Direct compact reserve decreases toward the moving sixth ceiling. -/
theorem thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_mono_sixth
    {q e6 e8 : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384)
    (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (8016 / 125 : ℝ) * (6512 / 5 - 480 * q)) :
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
        q (969 / 2 - 192 * q)
          ((8016 / 125 : ℝ) * (6512 / 5 - 480 * q)) e8 ≤
      thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
        q (969 / 2 - 192 * q) e6 e8 := by
  let M := (8016 / 125 : ℝ) * (6512 / 5 - 480 * q)
  have hMcore : 0 ≤ 6512 / 5 - 480 * q := by linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hcoeff := thetaCuspFirstAtomEighthScale695Over192_sixthLossCoefficient_pos hqlo hqhi
  have hgap : 0 ≤ M - e6 := by dsimp only [M]; linarith
  have hfactor : 0 ≤
      thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M := by positivity
  have hprod := mul_nonneg hgap hfactor
  have hid :
      thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
          q (969 / 2 - 192 * q) e6 e8 -
        thetaCuspFirstAtomEighthScale695Over192DirectJointReserve
          q (969 / 2 - 192 * q) M e8 =
        (M - e6) *
          (thetaCuspFullReflectionEighthCompactSixthCoefficient q + e6 + M) := by
    dsimp [thetaCuspFirstAtomEighthScale695Over192DirectJointReserve]
    ring
  dsimp only [M] at hprod hid ⊢
  linarith

/-- Direct compact reserve increases above the moving eighth floor. -/
theorem thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_mono_eighth
    {q e4 e6 e8 : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384)
    (he4 : 969 / 2 - 192 * q ≤ e4)
    (he8 : thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q ≤ e8) :
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve q e4 e6
        (thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q) ≤
      thetaCuspFirstAtomEighthScale695Over192DirectJointReserve q e4 e6 e8 := by
  have hbase := thetaCuspFirstAtomEighthScale695Over192_eighthGainCoefficient_pos hqlo hqhi
  have hcoeff : 0 ≤ thetaCuspFullReflectionEighthCompactEighthCoefficient q + e4 := by
    linarith
  have hgap : 0 ≤ e8 - thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q := by
    linarith
  rw [← sub_nonneg]
  dsimp [thetaCuspFirstAtomEighthScale695Over192DirectJointReserve]
  nlinarith [mul_nonneg hcoeff hgap]

/-- Exact direct-eighth joint chamber for admissible fourth, sixth, and eighth jets. -/
theorem thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_pos
    {q e4 e6 e8 : ℝ} (hqlo : (407 / 192 : ℝ) ≤ q) (hqhi : q ≤ 815 / 384)
    (he4 : 969 / 2 - 192 * q ≤ e4) (he6zero : 0 ≤ e6)
    (he6hi : e6 ≤ (8016 / 125 : ℝ) * (6512 / 5 - 480 * q))
    (he8 : thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q ≤ e8) :
    0 < thetaCuspFirstAtomEighthScale695Over192DirectJointReserve q e4 e6 e8 := by
  have hbase :=
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_pos_at_baseline hqlo hqhi
  have hsix :=
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_mono_sixth
      hqlo hqhi he6zero he6hi
        (e8 := thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q)
  have hprofileNonneg :=
    (thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile_pos hqlo hqhi).le
  have hfourth :=
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_mono_fourth
      hqlo hqhi he4 hprofileNonneg (e6 := e6)
  have heighth :=
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_mono_eighth
      hqlo hqhi he4 he8 (e6 := e6)
  linarith

/-- Physical compact reserve is positive on `695/192 ≤ A ≤ 1391/384`. -/
theorem thetaCuspFullReflectionEighthCompactReserve_pos_of_scale695Over192_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
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
  have hqlo : (407 / 192 : ℝ) ≤ q := by
    have h := hAlo
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have hqhi : q ≤ (815 / 384 : ℝ) := by
    have h := hAhi
    rw [show thetaCuspSingleAtomReflectionScale 1 x = q + 3 / 2 by
      simpa only [A] using hAq] at h
    linarith
  have he4 : 969 / 2 - 192 * q ≤ e4 := by
    have h := fourth695Over192AffineWeightFloor_lt_thetaCuspLikelihoodSourceLogPartitionJetFour
      hx hAlo hAhi
    simpa only [q, e4] using h.le
  have he6zero : 0 ≤ e6 := by
    simpa only [e6] using (thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx).le
  have he6hi : e6 ≤ (8016 / 125 : ℝ) * (6512 / 5 - 480 * q) := by
    have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale695Over192_affine_weight
      hx hAlo hAhi
    simpa only [q, e6] using h.le
  have hexp := thetaCuspLikelihoodFourthScale695Over192_expAffine_lt_exp_neg_three_mul
    (by simpa only [A] using hAlo) (by simpa only [A] using hAhi)
  have hexp' : (1 / 52050 : ℝ) * (1 - 3 * (A - 695 / 192)) <
      Real.exp (-(3 * A)) := by
    simpa only [A, neg_mul] using hexp
  have hApos : 0 < A := by dsimp only [A] at hAlo ⊢; linarith
  have heighthFloor :=
    fiveHundredFiftyThousand_mul_pow_eight_exp_lt_thetaCuspLikelihoodSourceLogPartitionJetEight_of_695Over192_le
      hx hAlo
  have he8 : thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q ≤ e8 := by
    have hlower :
        thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q <
          550000 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
      have hprofileEq :
          thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q =
            (550000 * A ^ (8 : ℕ)) *
              ((1 / 52050 : ℝ) * (1 - 3 * (A - 695 / 192))) := by
        dsimp only [thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile]
        rw [hAq]
        ring
      calc
        thetaCuspFirstAtomEighthScale695Over192DirectEighthProfile q =
            (550000 * A ^ (8 : ℕ)) *
              ((1 / 52050 : ℝ) * (1 - 3 * (A - 695 / 192))) := hprofileEq
        _ < (550000 * A ^ (8 : ℕ)) * Real.exp (-(3 * A)) :=
          mul_lt_mul_of_pos_left hexp' (by positivity)
        _ = 550000 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by ring
    have hfloor : 550000 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) < e8 := by
      simpa only [A, e8] using heighthFloor
    exact (hlower.trans hfloor).le
  have hjoint := thetaCuspFirstAtomEighthScale695Over192DirectJointReserve_pos
    hqlo hqhi he4 he6zero he6hi he8
  simpa [thetaCuspFullReflectionEighthCompactReserve,
    thetaCuspFirstAtomEighthScale695Over192DirectJointReserve, q, e4, e6, e8] using hjoint

/-- Native D1 is positive on `695/192 ≤ A ≤ 1391/384`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_scale695Over192_mem
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hreserve := thetaCuspFullReflectionEighthCompactReserve_pos_of_scale695Over192_mem
    hx hAlo hAhi
  have hlower := thetaCuspFullReflectionEighthCompactReserve_le_hankelCurvature hx
  linarith

/-- Native D1 is strict whenever first-atom weight is at least `407/192`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_407Over192_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (407 / 192 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqhi : thetaCuspBornWittenWeight 1 x ≤ (815 / 384 : ℝ)
  · have hscale : thetaCuspSingleAtomReflectionScale 1 x =
        thetaCuspBornWittenWeight 1 x + 3 / 2 := by
      dsimp only [thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAlo : (695 / 192 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x := by
      rw [hscale]
      linarith
    have hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ (1391 / 384 : ℝ) := by
      rw [hscale]
      linarith
    exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_scale695Over192_mem
      hx hAlo hAhi
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_815Over384_le_weight
      hx (le_of_not_ge hqhi)

/-- Exact Taylor certificate placing `x = 71/1000` above scale `695/192`. -/
theorem sixHundredNinetyFiveOneHundredNinetySeconds_lt_pi_mul_exp_oneHundredFortyTwoThousandths :
    (695 / 192 : ℝ) < Real.pi * Real.exp (71 / 500 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 71 / 500) 8
  have hp := Real.pi_gt_d20
  calc
    (695 / 192 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (∑ k ∈ Finset.range 8, (71 / 500 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.pi * Real.exp (71 / 500 : ℝ) := by gcongr

/-- Native D1 is strict on improved source half-line `x ≥ 71/1000`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_seventyOneThousandths_le
    {x : ℝ} (hx : (71 / 1000 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (71 / 500 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (695 / 192 : ℝ) < Real.pi * Real.exp (2 * x) :=
    sixHundredNinetyFiveOneHundredNinetySeconds_lt_pi_mul_exp_oneHundredFortyTwoThousandths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (407 / 192 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_407Over192_le_weight
    hx0 hqBound

end

end RHTower
