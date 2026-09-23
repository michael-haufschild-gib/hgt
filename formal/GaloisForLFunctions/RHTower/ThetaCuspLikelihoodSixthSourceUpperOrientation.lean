import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthSourceOrientation

/-!
# Upper orientation of the sixth theta likelihood source jet

The sixth logarithmic source jet is not merely positive.  Its positive three- and five-particle
grades are quadratically and quartically small in the literal higher-tail probability.  Since
that probability is below `1/400`, the complete logarithmic jet stays within `26/25` of its
one-particle ordinary sixth score.

This is same-aperture, coefficient-faithful control: every term is a normalized moment of the
fixed theta likelihood measure.  No Xi divisor or zero-location statement enters.
-/

namespace RHTower

noncomputable section

/-- The normalized one-particle ordinary sixth score of the higher theta likelihood source. -/
def thetaCuspLikelihoodSourceOrdinaryJetSix (x : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  64 * (A ^ (6 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 6 -
    15 * A ^ (5 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 5 +
    65 * A ^ (4 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 4 -
    90 * A ^ (3 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 3 +
    31 * A ^ (2 : ℕ) * thetaCuspLikelihoodNormalizedMoment B 2 -
    A * thetaCuspLikelihoodMean B)

set_option maxHeartbeats 2400000 in
/-- The literal sixth logarithmic source jet lies within three and one-half percent of its one-particle
ordinary score.  Positive odd particle grades cost only `O(p^(2 : ℕ))` and `O(p^(4 : ℕ))`, while every even
particle grade has the favorable sign. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (207 / 200 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let p := thetaCuspLikelihoodTailProbability B
  let e1 := thetaCuspLikelihoodMean B
  let e2 := thetaCuspLikelihoodNormalizedMoment B 2
  let e3 := thetaCuspLikelihoodNormalizedMoment B 3
  let e4 := thetaCuspLikelihoodNormalizedMoment B 4
  let e5 := thetaCuspLikelihoodNormalizedMoment B 5
  let e6 := thetaCuspLikelihoodNormalizedMoment B 6
  let b1 := 2 * A * e1
  let b2 := 4 * (A ^ (2 : ℕ) * e2 - A * e1)
  let b3 := 8 * (A ^ (3 : ℕ) * e3 - 3 * A ^ (2 : ℕ) * e2 + A * e1)
  let b4 := 16 * (A ^ (4 : ℕ) * e4 - 6 * A ^ (3 : ℕ) * e3 +
    7 * A ^ (2 : ℕ) * e2 - A * e1)
  let b5 := 32 * (A ^ (5 : ℕ) * e5 - 10 * A ^ (4 : ℕ) * e4 +
    25 * A ^ (3 : ℕ) * e3 - 15 * A ^ (2 : ℕ) * e2 + A * e1)
  let b6 := 64 * (A ^ (6 : ℕ) * e6 - 15 * A ^ (5 : ℕ) * e5 +
    65 * A ^ (4 : ℕ) * e4 - 90 * A ^ (3 : ℕ) * e3 +
    31 * A ^ (2 : ℕ) * e2 - A * e1)
  let q2 := 6 * b1 * b5 + 15 * b2 * b4 + 10 * b3 ^ (2 : ℕ)
  let q3 := 15 * b1 ^ (2 : ℕ) * b4 + 60 * b1 * b2 * b3 + 15 * b2 ^ (3 : ℕ)
  let q4 := 20 * b1 ^ (3 : ℕ) * b3 + 45 * b1 ^ (2 : ℕ) * b2 ^ (2 : ℕ)
  let q5 := 15 * b1 ^ (4 : ℕ) * b2
  let q6 := b1 ^ (6 : ℕ)
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx
  have hA0 : 0 < A := by linarith
  have he1 : 0 < e1 := by
    simpa only [e1] using thetaCuspLikelihoodMean_pos hB
  have he2 : 0 < e2 := by
    simpa only [e2] using thetaCuspLikelihoodNormalizedMoment_two_pos hB
  have he12 : 3 * e1 ≤ e2 := by
    have h := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 1
    simpa only [thetaCuspLikelihoodNormalizedMoment_one_eq_mean, e1, e2] using h
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
  have hpSmall : 400 * p < 1 := by
    simpa only [B, p] using
      four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have h22 : e2 ^ (2 : ℕ) ≤ p * e4 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 2
    simpa only [B, p, e2, e4, show 2 + 2 = 4 by norm_num, pow_two] using h
  have hp : 0 < p := by nlinarith [sq_pos_of_pos he2]
  have hp0 : 0 ≤ p := hp.le
  have h11 : e1 ^ (2 : ℕ) ≤ p * e2 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 1
    simpa only [B, p, e1, e2, thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 1 = 2 by norm_num, pow_two] using h
  have h12 : e1 * e2 ≤ p * e3 := by
    simpa only [B, p, e1, e2, e3,
      thetaCuspLikelihoodNormalizedMoment_one_eq_mean,
      show 1 + 2 = 3 by norm_num] using
        thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 1 2
  have h24 : e2 * e4 ≤ p * e6 := by
    simpa only [B, p, e2, e4, e6, show 2 + 4 = 6 by norm_num] using
      thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 2 4
  have h33 : e3 ^ (2 : ℕ) ≤ p * e6 := by
    have h := thetaCuspLikelihoodNormalizedMoment_mul_le_tailProbability_mul hB 3 3
    simpa only [B, p, e3, e6, show 3 + 3 = 6 by norm_num, pow_two] using h
  have he114 : e1 ^ (2 : ℕ) * e4 ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e1 ^ (2 : ℕ) * e4 ≤ (p * e2) * e4 :=
        mul_le_mul_of_nonneg_right h11 he4.le
      _ = p * (e2 * e4) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h24 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he123 : e1 * e2 * e3 ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e1 * e2 * e3 ≤ (p * e3) * e3 :=
        mul_le_mul_of_nonneg_right h12 he3.le
      _ = p * e3 ^ (2 : ℕ) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h33 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he23cube : e2 ^ (3 : ℕ) ≤ p ^ (2 : ℕ) * e6 := by
    calc
      e2 ^ (3 : ℕ) = e2 * e2 ^ (2 : ℕ) := by ring
      _ ≤ e2 * (p * e4) := mul_le_mul_of_nonneg_left h22 he2.le
      _ = p * (e2 * e4) := by ring
      _ ≤ p * (p * e6) := mul_le_mul_of_nonneg_left h24 hp0
      _ = p ^ (2 : ℕ) * e6 := by ring
  have he112 : e1 ^ (4 : ℕ) * e2 ≤ p ^ (4 : ℕ) * e6 := by
    calc
      e1 ^ (4 : ℕ) * e2 = (e1 ^ (2 : ℕ)) ^ (2 : ℕ) * e2 := by ring
      _ ≤ (p * e2) ^ (2 : ℕ) * e2 := by
        gcongr
      _ = p ^ (2 : ℕ) * e2 ^ (3 : ℕ) := by ring
      _ ≤ p ^ (2 : ℕ) * (p ^ (2 : ℕ) * e6) :=
        mul_le_mul_of_nonneg_left he23cube (sq_nonneg p)
      _ = p ^ (4 : ℕ) * e6 := by ring
  have hAe2 : e1 < A * e2 := by
    have hmul := mul_lt_mul_of_pos_right hA he2
    nlinarith
  have hAe3 : 3 * e2 < A * e3 := by
    have hmul := mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hAe4 : 6 * e3 < A * e4 := by
    have hmul := mul_lt_mul_of_pos_right hA he4
    nlinarith
  have hb1 : 0 < b1 := by dsimp only [b1]; positivity
  have hb1Upper : b1 ≤ 2 * A * e1 := by rfl
  have hb2 : 0 < b2 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hb2Upper : b2 ≤ 4 * A ^ (2 : ℕ) * e2 := by
    dsimp only [b2]
    nlinarith [mul_pos hA0 he1]
  have hb3 : 0 < b3 := by
    have hmul := mul_lt_mul_of_pos_left hAe3 (pow_pos hA0 2)
    dsimp only [b3]
    nlinarith [mul_pos hA0 he1]
  have hb3Upper : b3 ≤ 8 * A ^ (3 : ℕ) * e3 := by
    have hmul := mul_lt_mul_of_pos_left hAe2 hA0
    dsimp only [b3]
    nlinarith
  have hb4 : 0 < b4 := by
    have hmul := mul_lt_mul_of_pos_left hAe4 (pow_pos hA0 3)
    have htail : A * e1 < 7 * A ^ (2 : ℕ) * e2 := by
      have h := mul_lt_mul_of_pos_left hAe2 hA0
      nlinarith
    dsimp only [b4]
    nlinarith
  have hseven : 7 * e2 ≤ 6 * A * e3 := by
    have hAe3' : 3 * e3 < A * e3 := by
      exact mul_lt_mul_of_pos_right hA he3
    nlinarith
  have hsevenScaled := mul_le_mul_of_nonneg_left hseven (sq_nonneg A)
  have hb4Upper : b4 ≤ 16 * A ^ (4 : ℕ) * e4 := by
    dsimp only [b4]
    nlinarith [mul_pos hA0 he1]
  have hb5Lower : (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5 ≤ b5 := by
    have h := one_sixth_mul_likelihoodSourceLinearFive_le hx
    dsimp only [A, B, e1, e2, e3, e4, e5, b5] at h ⊢
    nlinarith
  have hb5 : 0 < b5 := by
    exact lt_of_lt_of_le (by positivity :
      0 < (32 / 6 : ℝ) * A ^ (5 : ℕ) * e5) hb5Lower
  have hb6Lower : (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6 ≤ b6 := by
    have h := one_thirtieth_mul_likelihoodSourceLinearSix_le hx
    dsimp only [A, B, e1, e2, e3, e4, e5, e6, b6] at h ⊢
    nlinarith
  have hb6 : 0 < b6 := by
    exact lt_of_lt_of_le (by positivity :
      0 < (64 / 30 : ℝ) * A ^ (6 : ℕ) * e6) hb6Lower
  have hb1SqB4 : b1 ^ (2 : ℕ) * b4 ≤ 64 * A ^ (6 : ℕ) * (e1 ^ (2 : ℕ) * e4) := by
    calc
      b1 ^ (2 : ℕ) * b4 ≤ (2 * A * e1) ^ (2 : ℕ) * (16 * A ^ (4 : ℕ) * e4) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 ^ (2 : ℕ) * e4) := by ring
  have hb1B2B3 : b1 * b2 * b3 ≤ 64 * A ^ (6 : ℕ) * (e1 * e2 * e3) := by
    calc
      b1 * b2 * b3 ≤ (2 * A * e1) * (4 * A ^ (2 : ℕ) * e2) *
          (8 * A ^ (3 : ℕ) * e3) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 * e2 * e3) := by ring
  have hb2Cube : b2 ^ (3 : ℕ) ≤ 64 * A ^ (6 : ℕ) * e2 ^ (3 : ℕ) := by
    calc
      b2 ^ (3 : ℕ) ≤ (4 * A ^ (2 : ℕ) * e2) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hb2.le hb2Upper 3
      _ = 64 * A ^ (6 : ℕ) * e2 ^ (3 : ℕ) := by ring
  have hq3 : q3 ≤ 2700 * p ^ (2 : ℕ) * b6 := by
    have hterm1 : 15 * b1 ^ (2 : ℕ) * b4 ≤ 960 * A ^ (6 : ℕ) * p ^ (2 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1SqB4 (by norm_num : (0 : ℝ) ≤ 15)
      have h2 := mul_le_mul_of_nonneg_left he114
        (show 0 ≤ 960 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hterm2 : 60 * b1 * b2 * b3 ≤ 3840 * A ^ (6 : ℕ) * p ^ (2 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1B2B3 (by norm_num : (0 : ℝ) ≤ 60)
      have h2 := mul_le_mul_of_nonneg_left he123
        (show 0 ≤ 3840 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hterm3 : 15 * b2 ^ (3 : ℕ) ≤ 960 * A ^ (6 : ℕ) * p ^ (2 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb2Cube (by norm_num : (0 : ℝ) ≤ 15)
      have h2 := mul_le_mul_of_nonneg_left he23cube
        (show 0 ≤ 960 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hlead := mul_le_mul_of_nonneg_left hb6Lower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2700) (sq_nonneg p))
    dsimp only [q3]
    nlinarith
  have hb1FourB2 : b1 ^ (4 : ℕ) * b2 ≤ 64 * A ^ (6 : ℕ) * (e1 ^ (4 : ℕ) * e2) := by
    calc
      b1 ^ (4 : ℕ) * b2 ≤ (2 * A * e1) ^ (4 : ℕ) * (4 * A ^ (2 : ℕ) * e2) := by gcongr
      _ = 64 * A ^ (6 : ℕ) * (e1 ^ (4 : ℕ) * e2) := by ring
  have hq5 : q5 ≤ 450 * p ^ (4 : ℕ) * b6 := by
    have hterm : 15 * b1 ^ (4 : ℕ) * b2 ≤ 960 * A ^ (6 : ℕ) * p ^ (4 : ℕ) * e6 := by
      have h1 := mul_le_mul_of_nonneg_left hb1FourB2 (by norm_num : (0 : ℝ) ≤ 15)
      have h2 := mul_le_mul_of_nonneg_left he112
        (show 0 ≤ 960 * A ^ (6 : ℕ) by positivity)
      nlinarith
    have hlead := mul_le_mul_of_nonneg_left hb6Lower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 450) (pow_nonneg hp0 4))
    dsimp only [q5]
    nlinarith
  have hq2nonneg : 0 ≤ q2 := by dsimp only [q2]; positivity
  have hq4nonneg : 0 ≤ q4 := by dsimp only [q4]; positivity
  have hq6nonneg : 0 ≤ q6 := by dsimp only [q6]; positivity
  have hpLt : p < (1 / 400 : ℝ) := by nlinarith
  have hp2 : p ^ (2 : ℕ) < (1 / 400 : ℝ) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hpLt hp0 (by norm_num)
  have hp4 : p ^ (4 : ℕ) < (1 / 400 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hpLt hp0 (by norm_num)
  have hbudget : 1 + 5400 * p ^ (2 : ℕ) + 10800 * p ^ (4 : ℕ) < (207 / 200 : ℝ) := by
    norm_num at hp2 hp4 ⊢
    nlinarith
  have hupper : b6 + 2 * q3 + 24 * q5 < (207 / 200 : ℝ) * b6 := by
    have hscaled := mul_lt_mul_of_pos_right hbudget hb6
    nlinarith
  have hdecomp :
      thetaCuspLikelihoodSourceLogPartitionJetSix x =
        b6 - q2 + 2 * q3 - 6 * q4 + 24 * q5 - 120 * q6 := by
    dsimp only [b1, b2, b3, b4, b5, b6, q2, q3, q4, q5, q6,
      A, B, e1, e2, e3, e4, e5, e6]
    unfold thetaCuspLikelihoodSourceLogPartitionJetSix
      thetaCuspLikelihoodSixthCumulant thetaCuspLikelihoodFifthCumulant
      thetaCuspLikelihoodFourthCumulant thetaCuspLikelihoodThirdCumulant
    rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
    unfold thetaCuspLikelihoodNormalizedMoment
    ring
  rw [hdecomp]
  change b6 - q2 + 2 * q3 - 6 * q4 + 24 * q5 - 120 * q6 <
    (207 / 200 : ℝ) * b6
  nlinarith

/-- The one-particle ordinary sixth source score is strictly positive. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetSix_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hB : 0 < B := by
    simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have he6 : 0 < thetaCuspLikelihoodNormalizedMoment B 6 := by
    have h2 := thetaCuspLikelihoodNormalizedMoment_two_pos hB
    have h23 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 2
    have h34 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 3
    have h45 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
    have h56 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
    nlinarith
  have h := one_thirtieth_mul_likelihoodSourceLinearSix_le hx
  dsimp only [thetaCuspLikelihoodSourceOrdinaryJetSix, A, B]
  have hlead : 0 < (64 / 30 : ℝ) * A ^ (6 : ℕ) *
      thetaCuspLikelihoodNormalizedMoment B 6 := by positivity
  dsimp only [A, B] at hlead
  nlinarith

/-- Compatibility form of the earlier four-percent sixth-jet upper orientation. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twentySixTwentyFifths_ordinary
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (26 / 25 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := by
  have hsharp :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  have hord := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
  nlinarith

end

end RHTower
