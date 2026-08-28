import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleThirtyOneEighthsBound

/-!
# Scale-twenty-three-sixths local bound for the sixth theta likelihood jet

The global sixth-jet estimate freezes the dominant square-gap score at the modular seam. Once
the source scale reaches `A = 23/6`, recentering the exact shifted score at `5/2` exposes stronger
exponential decay. Exact point/ray envelopes bound the dominant mass by `201`, complete score
integral by `212`, and literal logarithmic sixth jet by `14200`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Point-score exponential envelope after recentering at shifted coordinate `5/2`. -/
theorem thetaLikelihoodSixthScoreShift_scaleTwentyThreeSixths_envelope
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreShift (5 / 2 + s) ≤ 310000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
      s ^ 5 / 120 + s ^ 6 / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp : thetaLikelihoodSixthScoreShift (5 / 2 + s) ≤
      310000 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
        s ^ 5 / 120 + s ^ 6 / 720) := by
    dsimp [thetaLikelihoodSixthScoreShift]
    ring_nf
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs4 : 0 ≤ s ^ 4 := by positivity
    have hs5 : 0 ≤ s ^ 5 := by positivity
    have hs6 : 0 ≤ s ^ 6 := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

/-- Ray-transform exponential envelope in the scale-twenty-three-sixths ratio chamber `A/B ≤ 23/14`. -/
theorem thetaLikelihoodSixthScoreRayTransformPolynomial_scaleTwentyThreeSixths_envelope
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreRayTransformPolynomial (23 / 14) (5 / 2 + s) ≤
      1850000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
      s ^ 5 / 120 + s ^ 6 / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp :
      thetaLikelihoodSixthScoreRayTransformPolynomial (23 / 14) (5 / 2 + s) ≤
        1850000 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
          s ^ 5 / 120 + s ^ 6 / 720) := by
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    ring_nf
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs4 : 0 ≤ s ^ 4 := by positivity
    have hs5 : 0 ≤ s ^ 5 := by positivity
    have hs6 : 0 ≤ s ^ 6 := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

/-- Elementary rational enclosure for the recentered scale-`23/6` exponential. -/
theorem exp_neg_twentyThreeHalves_lt_ninetySixThousand :
    Real.exp (-(23 / 2 : ℝ)) < (1 / 96000 : ℝ) := by
  have hpow : Real.exp (-1) ^ 11 < (0.3678794412 : ℝ) ^ 11 :=
    pow_lt_pow_left₀ Real.exp_neg_one_lt_d9 (Real.exp_pos (-1)).le (by norm_num)
  have h11 : Real.exp (-11) < (1 / 59000 : ℝ) := by
    rw [show (-11 : ℝ) = (11 : ℕ) * (-1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact hpow.trans (by norm_num)
  have hhalf : Real.exp (-(1 / 2 : ℝ)) < (61 / 100 : ℝ) := by
    have he := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 1 / 2) 4
    have hb : (100 / 61 : ℝ) < Real.exp (1 / 2) := by
      calc
        (100 / 61 : ℝ) <
            ∑ k ∈ Finset.range 4, (1 / 2 : ℝ) ^ k / k.factorial := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
        _ ≤ Real.exp (1 / 2) := he
    have hprod : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2 : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]
  rw [show (-(23 / 2 : ℝ)) = -11 + -(1 / 2 : ℝ) by norm_num, Real.exp_add]
  nlinarith [Real.exp_pos (-11), Real.exp_pos (-(1 / 2 : ℝ))]

/-- Above source scale twenty-three sixths, the exact dominant square-gap sixth-score mass is below `201`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_twoHundredOne_of_twentyThreeSixths_le
    (A : ℝ) {B : ℝ} (hA : (23 / 6 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B < 201 := by
  have hB : 0 < B := by rw [hBA]; linarith
  let s := 3 * A - 23 / 2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hy : 3 * A - 9 = 5 / 2 + s := by dsimp [s]; ring
  have hr0 : 0 ≤ A / B := div_nonneg (by linarith) hB.le
  have hr : A / B ≤ (23 / 14 : ℝ) := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    nlinarith
  have hpinv : 1 / B ≤ (3 / 7 : ℝ) := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    nlinarith
  have hy0 : 0 ≤ 3 * A - 9 := by linarith
  have hqmono :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9) ≤
        thetaLikelihoodSixthScoreRayTransformPolynomial (23 / 14) (3 * A - 9) := by
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
        1850000 * Real.exp s := by
    calc
      _ ≤ thetaLikelihoodSixthScoreRayTransformPolynomial (23 / 14) (3 * A - 9) := hqmono
      _ = thetaLikelihoodSixthScoreRayTransformPolynomial (23 / 14) (5 / 2 + s) := by rw [hy]
      _ ≤ _ := thetaLikelihoodSixthScoreRayTransformPolynomial_scaleTwentyThreeSixths_envelope hs
  have hp : thetaLikelihoodSixthScore (3 * A) ≤ 310000 * Real.exp s := by
    rw [thetaLikelihoodSixthScore_eq_shiftNine, hy]
    exact thetaLikelihoodSixthScoreShift_scaleTwentyThreeSixths_envelope hs
  have hpoint :
      16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScore (3 * A) * Real.exp (-(3 * B))) ≤
        (16 * 310000) * Real.exp (-(23 / 2 : ℝ)) := by
    calc
      _ ≤ 16 * Real.exp (-(9 / 2 : ℝ)) *
          ((310000 * Real.exp s) * Real.exp (-(3 * B))) := by gcongr
      _ = _ := by
        rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
            ((310000 * Real.exp s) * Real.exp (-(3 * B))) =
          16 * 310000 * (Real.exp (-(9 / 2 : ℝ)) *
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
          (18 * (3 / 7 : ℝ) * 1850000) * Real.exp (-(23 / 2 : ℝ)) := by
    calc
      _ ≤ 18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (3 / 7 : ℝ) *
            (1850000 * Real.exp s)) := by
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
                (Real.exp (-(3 * B)) * (3 / 7 : ℝ) *
                  thetaLikelihoodSixthScoreRayTransformPolynomial
                    (A / B) (3 * A - 9)) := by gcongr
            _ ≤ _ := by gcongr
      _ = _ := by
        rw [show 18 * Real.exp (-(9 / 2 : ℝ)) *
            (Real.exp (-(3 * B)) * (3 / 7 : ℝ) *
              (1850000 * Real.exp s)) =
          (18 * (3 / 7 : ℝ) * 1850000) *
            (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) *
              Real.exp s) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [hBA]
        dsimp [s]
        ring
  rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB]
  have he := exp_neg_twentyThreeHalves_lt_ninetySixThousand
  nlinarith

/-- Above scale twenty-three sixths, dominant plus stable sixth-score mass is below `212`. -/
theorem integral_thetaLikelihoodSixthScore_lt_twoHundredTwelve_of_twentyThreeSixths_le_scale
    {x : ℝ} (hx : 0 ≤ x) (hATwentyThreeSixths : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore
            (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) < 212 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 23 / 6)).le.trans hATwentyThreeSixths
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd :=
    thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_twoHundredOne_of_twentyThreeSixths_le A hATwentyThreeSixths hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_le hApi hBA
  have hpi2 : Real.pi ^ 2 < (10 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi6 : Real.pi ^ 6 < (1000 : ℝ) := by
    have h := pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Real.pi ^ 6 = (Real.pi ^ 2) ^ 3 := by ring
      _ < (10 : ℝ) ^ 3 := h
      _ = 1000 := by norm_num
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Scale-local improvement of the literal logarithmic sixth likelihood budget. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_fourteenThousandTwoHundred_of_twentyThreeSixths_le_scale
    {x : ℝ} (hx : 0 ≤ x) (hATwentyThreeSixths : (23 / 6 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x < 14200 := by
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hscore := integral_thetaLikelihoodSixthScore_lt_twoHundredTwelve_of_twentyThreeSixths_le_scale hx hATwentyThreeSixths
  have hordinary : thetaCuspLikelihoodSourceOrdinaryJetSix x < 64 * 212 := by
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
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twentySixTwentyFifths_ordinary hx
  nlinarith

end

end RHTower
