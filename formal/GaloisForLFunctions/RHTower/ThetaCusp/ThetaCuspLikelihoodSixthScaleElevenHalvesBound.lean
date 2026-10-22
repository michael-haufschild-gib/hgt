import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthScaleSixBound

/-!
# Scale-eleven-halves local bound for the sixth theta likelihood jet

Recenter the exact dominant sixth score at source scale `A = 11/2`.  Coefficientwise exponential
envelopes reduce the dominant score mass below `16`; the stable tower then puts the complete score
integral below `27` and the literal logarithmic sixth jet below `1800`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Point-score exponential envelope recentered at source scale `11/2`. -/
theorem thetaLikelihoodSixthScoreShift_scaleElevenHalves_envelope
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreShift (15 / 2 + s) ≤ 7000000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ (2 : ℕ) / 2 + s ^ (3 : ℕ) / 6 + s ^ (4 : ℕ) / 24 +
      s ^ (5 : ℕ) / 120 + s ^ (6 : ℕ) / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp : thetaLikelihoodSixthScoreShift (15 / 2 + s) ≤
      7000000 * (1 + s + s ^ (2 : ℕ) / 2 + s ^ (3 : ℕ) / 6 + s ^ (4 : ℕ) / 24 +
        s ^ (5 : ℕ) / 120 + s ^ (6 : ℕ) / 720) := by
    dsimp [thetaLikelihoodSixthScoreShift]
    ring_nf
    have hs2 : 0 ≤ s ^ (2 : ℕ) := by positivity
    have hs3 : 0 ≤ s ^ (3 : ℕ) := by positivity
    have hs4 : 0 ≤ s ^ (4 : ℕ) := by positivity
    have hs5 : 0 ≤ s ^ (5 : ℕ) := by positivity
    have hs6 : 0 ≤ s ^ (6 : ℕ) := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

/-- Ray-transform envelope in the exact ratio chamber `A/B ≤ 11/8`. -/
theorem thetaLikelihoodSixthScoreRayTransformPolynomial_scaleElevenHalves_envelope
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreRayTransformPolynomial (11 / 8) (15 / 2 + s) ≤
      24000000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ (2 : ℕ) / 2 + s ^ (3 : ℕ) / 6 + s ^ (4 : ℕ) / 24 +
      s ^ (5 : ℕ) / 120 + s ^ (6 : ℕ) / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp :
      thetaLikelihoodSixthScoreRayTransformPolynomial (11 / 8) (15 / 2 + s) ≤
        24000000 * (1 + s + s ^ (2 : ℕ) / 2 + s ^ (3 : ℕ) / 6 + s ^ (4 : ℕ) / 24 +
          s ^ (5 : ℕ) / 120 + s ^ (6 : ℕ) / 720) := by
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    ring_nf
    have hs2 : 0 ≤ s ^ (2 : ℕ) := by positivity
    have hs3 : 0 ≤ s ^ (3 : ℕ) := by positivity
    have hs4 : 0 ≤ s ^ (4 : ℕ) := by positivity
    have hs5 : 0 ≤ s ^ (5 : ℕ) := by positivity
    have hs6 : 0 ≤ s ^ (6 : ℕ) := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

/-- Seventh-order Taylor upper enclosure used to shift the scale-six exponential estimate. -/
theorem exp_threeQuarters_lt_twoHundredSeventyOneOneHundredTwentyEighths :
    Real.exp (3 / 4 : ℝ) < 271 / 128 := by
  have hb := Real.exp_bound (x := (3 / 4 : ℝ)) (by norm_num)
    (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  nlinarith [le_abs_self
    (Real.exp (3 / 4 : ℝ) -
      (1 + (3 / 4 : ℝ) + (3 / 4 : ℝ) ^ (2 : ℕ) / 2 +
        (3 / 4 : ℝ) ^ (3 : ℕ) / 6 + (3 / 4 : ℝ) ^ (4 : ℕ) / 24 +
        (3 / 4 : ℝ) ^ (5 : ℕ) / 120 + (3 / 4 : ℝ) ^ (6 : ℕ) / 720))]

/-- Rational upper enclosure for the scale shift `exp(3/2)`. -/
theorem exp_threeHalves_lt_nineHalves : Real.exp (3 / 2 : ℝ) < 9 / 2 := by
  rw [show (3 / 2 : ℝ) = 3 / 4 + 3 / 4 by ring, Real.exp_add]
  nlinarith [exp_threeQuarters_lt_twoHundredSeventyOneOneHundredTwentyEighths,
    Real.exp_pos (3 / 4 : ℝ)]

/-- Elementary rational enclosure for the recentered exponential. -/
theorem exp_neg_thirtyThreeHalves_lt_oneFourteenMillion :
    Real.exp (-(33 / 2 : ℝ)) < (1 / 14000000 : ℝ) := by
  rw [show (-(33 / 2 : ℝ)) = -18 + 3 / 2 by ring, Real.exp_add]
  have h18 := exp_neg_eighteen_lt_oneSixtyFourMillion
  have h32 := exp_threeHalves_lt_nineHalves
  have h18pos := Real.exp_pos (-18)
  have h32pos := Real.exp_pos (3 / 2 : ℝ)
  nlinarith

/-- Above source scale `11/2`, the dominant sixth-score mass is below `16`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_sixteen_of_elevenHalves_le
    (A : ℝ) {B : ℝ} (hA : (11 / 2 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B < 16 := by
  have hB : 0 < B := by rw [hBA]; linarith
  let s := 3 * A - 33 / 2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hy : 3 * A - 9 = 15 / 2 + s := by dsimp [s]; ring
  have hr0 : 0 ≤ A / B := div_nonneg (by linarith) hB.le
  have hr : A / B ≤ (11 / 8 : ℝ) := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    nlinarith
  have hpinv : 1 / B ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    nlinarith
  have hy0 : 0 ≤ 3 * A - 9 := by linarith
  have hqmono :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9) ≤
        thetaLikelihoodSixthScoreRayTransformPolynomial (11 / 8) (3 * A - 9) := by
    dsimp only [thetaLikelihoodSixthScoreRayTransformPolynomial]
    have hp1 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivOne (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivOne]
      positivity
    have hp2 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivTwo (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivTwo]
      positivity
    have hp3 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivThree (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivThree]
      positivity
    have hp4 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivFour (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivFour]
      positivity
    have hp5 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivFive (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivFive]
      positivity
    have hp6 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivSix (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivSix]
      positivity
    have hr2 := pow_le_pow_left₀ hr0 hr 2
    have hr3 := pow_le_pow_left₀ hr0 hr 3
    have hr4 := pow_le_pow_left₀ hr0 hr 4
    have hr5 := pow_le_pow_left₀ hr0 hr 5
    have hr6 := pow_le_pow_left₀ hr0 hr 6
    nlinarith [mul_le_mul_of_nonneg_right hr hp1,
      mul_le_mul_of_nonneg_right hr2 hp2,
      mul_le_mul_of_nonneg_right hr3 hp3,
      mul_le_mul_of_nonneg_right hr4 hp4,
      mul_le_mul_of_nonneg_right hr5 hp5,
      mul_le_mul_of_nonneg_right hr6 hp6]
  have hq :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9) ≤
        24000000 * Real.exp s := by
    calc
      _ ≤ thetaLikelihoodSixthScoreRayTransformPolynomial (11 / 8) (3 * A - 9) := hqmono
      _ = thetaLikelihoodSixthScoreRayTransformPolynomial (11 / 8) (15 / 2 + s) := by rw [hy]
      _ ≤ _ := thetaLikelihoodSixthScoreRayTransformPolynomial_scaleElevenHalves_envelope hs
  have hp : thetaLikelihoodSixthScore (3 * A) ≤ 7000000 * Real.exp s := by
    rw [thetaLikelihoodSixthScore_eq_shiftNine, hy]
    exact thetaLikelihoodSixthScoreShift_scaleElevenHalves_envelope hs
  have hpoint :
      16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScore (3 * A) * Real.exp (-(3 * B))) ≤
        (16 * 7000000) * Real.exp (-(33 / 2 : ℝ)) := by
    calc
      _ ≤ 16 * Real.exp (-(9 / 2 : ℝ)) *
          ((7000000 * Real.exp s) * Real.exp (-(3 * B))) := by gcongr
      _ = _ := by
        rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
            ((7000000 * Real.exp s) * Real.exp (-(3 * B))) =
          16 * 7000000 * (Real.exp (-(9 / 2 : ℝ)) *
            Real.exp (-(3 * B)) * Real.exp s) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [hBA]
        dsimp [s]
        ring
  have hray :
      18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9)) ≤
        (18 * (1 / 4 : ℝ) * 24000000) * Real.exp (-(33 / 2 : ℝ)) := by
    calc
      _ ≤ 18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (1 / 4 : ℝ) *
            (24000000 * Real.exp s)) := by
          have hq0 : 0 ≤ thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (3 * A - 9) := by
            dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
              thetaLikelihoodSixthScoreShift,
              thetaLikelihoodSixthScoreShiftDerivOne,
              thetaLikelihoodSixthScoreShiftDerivTwo,
              thetaLikelihoodSixthScoreShiftDerivThree,
              thetaLikelihoodSixthScoreShiftDerivFour,
              thetaLikelihoodSixthScoreShiftDerivFive,
              thetaLikelihoodSixthScoreShiftDerivSix]
            positivity
          calc
            _ = 18 * Real.exp (-(9 / 2 : ℝ)) *
                (Real.exp (-(3 * B)) * (1 / B) *
                  thetaLikelihoodSixthScoreRayTransformPolynomial
                    (A / B) (3 * A - 9)) := by ring
            _ ≤ 18 * Real.exp (-(9 / 2 : ℝ)) *
                (Real.exp (-(3 * B)) * (1 / 4 : ℝ) *
                  thetaLikelihoodSixthScoreRayTransformPolynomial
                    (A / B) (3 * A - 9)) := by gcongr
            _ ≤ _ := by gcongr
      _ = _ := by
        rw [show 18 * Real.exp (-(9 / 2 : ℝ)) *
            (Real.exp (-(3 * B)) * (1 / 4 : ℝ) *
              (24000000 * Real.exp s)) =
          (18 * (1 / 4 : ℝ) * 24000000) *
            (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) *
              Real.exp s) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [hBA]
        dsimp [s]
        ring
  rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB]
  have he := exp_neg_thirtyThreeHalves_lt_oneFourteenMillion
  nlinarith [Real.exp_pos (-(33 / 2 : ℝ))]

/-- Above scale `11/2`, dominant plus stable sixth-score mass is below `27`. -/
theorem integral_thetaLikelihoodSixthScore_lt_twentySeven_of_elevenHalves_le_scale
    {x : ℝ} (hx : 0 ≤ x) (hA : 11 / 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) < 27 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 11 / 2)).le.trans hA
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd :=
    thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_sixteen_of_elevenHalves_le A hA hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_le hApi hBA
  have hpi2 : Real.pi ^ (2 : ℕ) < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi6 : Real.pi ^ (6 : ℕ) < (1000 : ℝ) := by
    have h := pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Real.pi ^ (6 : ℕ) = (Real.pi ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
      _ < (10 : ℝ) ^ (3 : ℕ) := h
      _ = 1000 := by norm_num
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Scale-local improvement of the literal logarithmic sixth likelihood budget. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_eighteenHundred_of_elevenHalves_le_scale
    {x : ℝ} (hx : 0 ≤ x) (hA : 11 / 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x < 1800 := by
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hscore :=
    integral_thetaLikelihoodSixthScore_lt_twentySeven_of_elevenHalves_le_scale hx hA
  have hordinary : thetaCuspLikelihoodSourceOrdinaryJetSix x < 64 * 27 := by
    have hordinaryPos := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx] at hordinaryPos
    have hcoeff : 0 < 64 / P := div_pos (by norm_num) hP
    have hcoeffUpper : 64 / P ≤ 64 := by
      apply (div_le_iff₀ hP).2
      nlinarith
    have hmass0 : 0 < (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left hscore hcoeff,
      mul_le_mul_of_nonneg_right hcoeffUpper hmass0.le]
  have hlog :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  nlinarith

end


end RHTower
