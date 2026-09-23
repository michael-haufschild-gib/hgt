import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthFockTraceConnector

/-!
# Exact Bell-grade decomposition of the eighth likelihood log jet

The literal eighth logarithmic jet splits into its ordinary one-particle jet and seven finite
Bell grades.  Odd particle grades are nonnegative on the physical source half-line.  Therefore
the remaining logarithmic burden is exactly the sum of four explicit negative even grades.
-/

namespace RHTower

noncomputable section

def thetaCuspLikelihoodEighthBellJetOne (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  2 * A * thetaCuspLikelihoodMean B

def thetaCuspLikelihoodEighthBellJetTwo (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  4 * (A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
    A * thetaCuspLikelihoodMean B)

def thetaCuspLikelihoodEighthBellJetThree (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  8 * (A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 -
    3 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 +
    A * thetaCuspLikelihoodMean B)

def thetaCuspLikelihoodEighthBellJetFour (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  16 * (A ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 -
    6 * A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 +
    7 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
    A * thetaCuspLikelihoodMean B)

def thetaCuspLikelihoodEighthBellJetFive (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  32 * (A ^ (5 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 5 -
    10 * A ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 +
    25 * A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 -
    15 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 +
    A * thetaCuspLikelihoodMean B)

def thetaCuspLikelihoodEighthBellJetSix (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  64 * (A ^ (6 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 6 -
    15 * A ^ (5 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 5 +
    65 * A ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 -
    90 * A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 +
    31 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
    A * thetaCuspLikelihoodMean B)

def thetaCuspLikelihoodEighthBellJetSeven (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  128 * (A ^ (7 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 7 -
    21 * A ^ (6 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 6 +
    140 * A ^ (5 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 5 -
    350 * A ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 +
    301 * A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 -
    63 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 +
    A * thetaCuspLikelihoodMean B)

def thetaCuspLikelihoodEighthBellJetEight (x : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceOrdinaryJetEight x

def thetaCuspLikelihoodEighthBellGradeTwo (x : ℝ) : ℝ :=
  8 * thetaCuspLikelihoodEighthBellJetOne x * thetaCuspLikelihoodEighthBellJetSeven x +
    28 * thetaCuspLikelihoodEighthBellJetTwo x * thetaCuspLikelihoodEighthBellJetSix x +
    56 * thetaCuspLikelihoodEighthBellJetThree x * thetaCuspLikelihoodEighthBellJetFive x +
    35 * thetaCuspLikelihoodEighthBellJetFour x ^ (2 : ℕ)

def thetaCuspLikelihoodEighthBellGradeThree (x : ℝ) : ℝ :=
  28 * thetaCuspLikelihoodEighthBellJetOne x ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthBellJetSix x +
    168 * thetaCuspLikelihoodEighthBellJetOne x *
      thetaCuspLikelihoodEighthBellJetTwo x * thetaCuspLikelihoodEighthBellJetFive x +
    280 * thetaCuspLikelihoodEighthBellJetOne x *
      thetaCuspLikelihoodEighthBellJetThree x * thetaCuspLikelihoodEighthBellJetFour x +
    210 * thetaCuspLikelihoodEighthBellJetTwo x ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthBellJetFour x +
    280 * thetaCuspLikelihoodEighthBellJetTwo x *
      thetaCuspLikelihoodEighthBellJetThree x ^ (2 : ℕ)

def thetaCuspLikelihoodEighthBellGradeFour (x : ℝ) : ℝ :=
  56 * thetaCuspLikelihoodEighthBellJetOne x ^ (3 : ℕ) *
      thetaCuspLikelihoodEighthBellJetFive x +
    420 * thetaCuspLikelihoodEighthBellJetOne x ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthBellJetTwo x * thetaCuspLikelihoodEighthBellJetFour x +
    280 * thetaCuspLikelihoodEighthBellJetOne x ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthBellJetThree x ^ (2 : ℕ) +
    840 * thetaCuspLikelihoodEighthBellJetOne x *
      thetaCuspLikelihoodEighthBellJetTwo x ^ (2 : ℕ) * thetaCuspLikelihoodEighthBellJetThree x +
    105 * thetaCuspLikelihoodEighthBellJetTwo x ^ (4 : ℕ)

def thetaCuspLikelihoodEighthBellGradeFive (x : ℝ) : ℝ :=
  70 * thetaCuspLikelihoodEighthBellJetOne x ^ (4 : ℕ) *
      thetaCuspLikelihoodEighthBellJetFour x +
    560 * thetaCuspLikelihoodEighthBellJetOne x ^ (3 : ℕ) *
      thetaCuspLikelihoodEighthBellJetTwo x * thetaCuspLikelihoodEighthBellJetThree x +
    420 * thetaCuspLikelihoodEighthBellJetOne x ^ (2 : ℕ) *
      thetaCuspLikelihoodEighthBellJetTwo x ^ (3 : ℕ)

def thetaCuspLikelihoodEighthBellGradeSix (x : ℝ) : ℝ :=
  56 * thetaCuspLikelihoodEighthBellJetOne x ^ (5 : ℕ) *
      thetaCuspLikelihoodEighthBellJetThree x +
    210 * thetaCuspLikelihoodEighthBellJetOne x ^ (4 : ℕ) *
      thetaCuspLikelihoodEighthBellJetTwo x ^ (2 : ℕ)

def thetaCuspLikelihoodEighthBellGradeSeven (x : ℝ) : ℝ :=
  28 * thetaCuspLikelihoodEighthBellJetOne x ^ (6 : ℕ) *
    thetaCuspLikelihoodEighthBellJetTwo x

def thetaCuspLikelihoodEighthBellGradeEight (x : ℝ) : ℝ :=
  thetaCuspLikelihoodEighthBellJetOne x ^ (8 : ℕ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Exact finite Bell-grade identity for the literal eighth logarithmic source jet. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetEight_eq_bellGrades (x : ℝ) :
    thetaCuspLikelihoodSourceLogPartitionJetEight x =
      thetaCuspLikelihoodEighthBellJetEight x -
        thetaCuspLikelihoodEighthBellGradeTwo x +
        2 * thetaCuspLikelihoodEighthBellGradeThree x -
        6 * thetaCuspLikelihoodEighthBellGradeFour x +
        24 * thetaCuspLikelihoodEighthBellGradeFive x -
        120 * thetaCuspLikelihoodEighthBellGradeSix x +
        720 * thetaCuspLikelihoodEighthBellGradeSeven x -
        5040 * thetaCuspLikelihoodEighthBellGradeEight x := by
  unfold thetaCuspLikelihoodEighthBellGradeTwo thetaCuspLikelihoodEighthBellGradeThree
    thetaCuspLikelihoodEighthBellGradeFour thetaCuspLikelihoodEighthBellGradeFive
    thetaCuspLikelihoodEighthBellGradeSix thetaCuspLikelihoodEighthBellGradeSeven
    thetaCuspLikelihoodEighthBellGradeEight
    thetaCuspLikelihoodEighthBellJetOne thetaCuspLikelihoodEighthBellJetTwo
    thetaCuspLikelihoodEighthBellJetThree thetaCuspLikelihoodEighthBellJetFour
    thetaCuspLikelihoodEighthBellJetFive thetaCuspLikelihoodEighthBellJetSix
    thetaCuspLikelihoodEighthBellJetSeven thetaCuspLikelihoodEighthBellJetEight
    thetaCuspLikelihoodSourceOrdinaryJetEight
    thetaCuspLikelihoodSourceLogPartitionJetEight
    thetaCuspLikelihoodEighthCumulant thetaCuspLikelihoodSeventhCumulant
    thetaCuspLikelihoodSixthCumulant thetaCuspLikelihoodFifthCumulant
    thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodThirdCumulant
  rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
  unfold thetaCuspLikelihoodNormalizedMoment
  ring

theorem thetaCuspLikelihoodEighthBellJets_one_to_six_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodEighthBellJetOne x ∧
    0 < thetaCuspLikelihoodEighthBellJetTwo x ∧
    0 < thetaCuspLikelihoodEighthBellJetThree x ∧
    0 < thetaCuspLikelihoodEighthBellJetFour x ∧
    0 < thetaCuspLikelihoodEighthBellJetFive x ∧
    0 < thetaCuspLikelihoodEighthBellJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    simpa only [e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
  have he23 : 3 * e2 ≤ e3 := by
    simpa only [e2, e3] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
  have he34 : 3 * e3 ≤ e4 := by
    simpa only [e3, e4] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
  have he45 : 3 * e4 ≤ e5 := by
    simpa only [e4, e5] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
  have he56 : 3 * e5 ≤ e6 := by
    simpa only [e5, e6] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
  have he3 : 0 < e3 := lt_of_lt_of_le (mul_pos (by norm_num) he2) he23
  have he4 : 0 < e4 := lt_of_lt_of_le (mul_pos (by norm_num) he3) he34
  have he5 : 0 < e5 := lt_of_lt_of_le (mul_pos (by norm_num) he4) he45
  have he6 : 0 < e6 := lt_of_lt_of_le (mul_pos (by norm_num) he5) he56
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hAe4 : 6 * e3 < A * e4 := by
    have hmul := mul_lt_mul_of_pos_right hA he4
    nlinarith
  have hb1 : 0 < thetaCuspLikelihoodEighthBellJetOne x := by
    dsimp only [thetaCuspLikelihoodEighthBellJetOne, A, B, e1]
    positivity
  have hb2 : 0 < thetaCuspLikelihoodEighthBellJetTwo x := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [thetaCuspLikelihoodEighthBellJetTwo, A, B, e1, e2]
    nlinarith [mul_pos hA0 he1]
  have hb3 : 0 < thetaCuspLikelihoodEighthBellJetThree x := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [thetaCuspLikelihoodEighthBellJetThree, A, B, e1, e2, e3]
    nlinarith [mul_pos hA0 he1]
  have hb4 : 0 < thetaCuspLikelihoodEighthBellJetFour x := by
    have hmul := mul_lt_mul_of_pos_left hAe4 (pow_pos hA0 3)
    have htail : A * e1 < 7 * A ^ (2 : ℕ) * e2 := by
      have h := mul_lt_mul_of_pos_left hAe2 hA0
      nlinarith
    dsimp only [thetaCuspLikelihoodEighthBellJetFour, A, B, e1, e2, e3, e4]
    nlinarith
  have hb5 : 0 < thetaCuspLikelihoodEighthBellJetFive x := by
    have h := one_sixth_mul_likelihoodSourceLinearFive_le hx
    have h' : (1 / 6 : ℝ) * A ^ (5 : ℕ) * e5 ≤
        A ^ (5 : ℕ) * e5 - 10 * A ^ (4 : ℕ) * e4 + 25 * A ^ (3 : ℕ) * e3 -
          15 * A ^ (2 : ℕ) * e2 + A * e1 := by
      simpa only [A, B, e1, e2, e3, e4, e5] using h
    have hlead : 0 < (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5 := by positivity
    dsimp only [thetaCuspLikelihoodEighthBellJetFive, A, B, e1, e2, e3, e4, e5]
    nlinarith
  have hb6 : 0 < thetaCuspLikelihoodEighthBellJetSix x := by
    have h := one_thirtieth_mul_likelihoodSourceLinearSix_le hx
    have h' : (1 / 30 : ℝ) * A ^ (6 : ℕ) * e6 ≤
        A ^ (6 : ℕ) * e6 - 15 * A ^ (5 : ℕ) * e5 + 65 * A ^ (4 : ℕ) * e4 -
          90 * A ^ (3 : ℕ) * e3 + 31 * A ^ (2 : ℕ) * e2 - A * e1 := by
      simpa only [A, B, e1, e2, e3, e4, e5, e6] using h
    have hlead : 0 < (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6 := by positivity
    dsimp only [thetaCuspLikelihoodEighthBellJetSix, A, B, e1, e2, e3, e4, e5, e6]
    nlinarith
  exact ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩

/-- Every favorable odd Bell grade is nonnegative. -/
theorem thetaCuspLikelihoodEighthBellOddGrades_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspLikelihoodEighthBellGradeThree x ∧
    0 ≤ thetaCuspLikelihoodEighthBellGradeFive x ∧
    0 ≤ thetaCuspLikelihoodEighthBellGradeSeven x := by
  rcases thetaCuspLikelihoodEighthBellJets_one_to_six_pos hx with
    ⟨h1, h2, h3, h4, h5, h6⟩
  constructor
  · unfold thetaCuspLikelihoodEighthBellGradeThree
    positivity
  constructor
  · unfold thetaCuspLikelihoodEighthBellGradeFive
    positivity
  · unfold thetaCuspLikelihoodEighthBellGradeSeven
    positivity

/-- Exact lower reduction: only four negative even Bell grades remain. -/
theorem thetaCuspLikelihoodEighthBellEvenLoss_lower_le_sourceLogJet
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthBellJetEight x -
        (thetaCuspLikelihoodEighthBellGradeTwo x +
          6 * thetaCuspLikelihoodEighthBellGradeFour x +
          120 * thetaCuspLikelihoodEighthBellGradeSix x +
          5040 * thetaCuspLikelihoodEighthBellGradeEight x) ≤
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  rcases thetaCuspLikelihoodEighthBellOddGrades_nonneg hx with ⟨h3, h5, h7⟩
  rw [thetaCuspLikelihoodSourceLogPartitionJetEight_eq_bellGrades]
  nlinarith

end

end RHTower
