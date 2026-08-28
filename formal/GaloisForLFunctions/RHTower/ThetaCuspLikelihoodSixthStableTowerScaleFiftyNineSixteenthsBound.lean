import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthStableTowerScaleEightyNineTwentyFourthsBound

/-!
# Scale-59/16 half-unit bound for the stable sixth-score tower

The stable-edge factor still gains `1/20` over its frozen π-envelope from scale `59/16`.
Keeping the existing exact tail constant and sharpening only the final π estimate then shows
that the complete stable tower is strictly below `1/2`, rather than merely below one.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Elementary exponential input for the scale-`59/16` gain. -/
theorem exp_neg_thirteenThirds_lt_oneSixtieth :
    Real.exp (-(13 / 3 : ℝ)) < (1 / 60 : ℝ) := by
  have hpow : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have hfour : (160 / 3 : ℝ) < Real.exp 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (160 / 3 : ℝ) < (2.7182818283 : ℝ) ^ 4).trans hpow
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) 2
  have hthird : (4 / 3 : ℝ) ≤ Real.exp (1 / 3) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at he ⊢
    exact he
  have hlarge : (60 : ℝ) < Real.exp (13 / 3) := by
    rw [show (13 / 3 : ℝ) = 4 + 1 / 3 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (4 : ℝ), Real.exp_pos (1 / 3 : ℝ)]
  have hprod : Real.exp (-(13 / 3 : ℝ)) * Real.exp (13 / 3 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(13 / 3 : ℝ))]

/-- Above `59/16`, stable-edge scale decay gains a factor `1/20` over the π envelope. -/
theorem thetaSixthScalePowExp_le_oneTwentieth_pi_of_59Over16_le
    {A d : ℝ} (hA : (59 / 16 : ℝ) ≤ A) (hd : 8 ≤ d) :
    A ^ 6 * Real.exp (-A * d) ≤
      (1 / 20 : ℝ) * Real.pi ^ 6 * Real.exp (-Real.pi * d) := by
  have hd0 : 0 < d := by linarith
  have hmono := thetaSixthScalePowExp_le_of_scale_ge
    (a := (59 / 16 : ℝ)) (A := A) (d := d) (by
      apply (div_le_iff₀ hd0).2
      nlinarith) hA hd0
  have hpi6lo : (3.1415 : ℝ) ^ 6 < Real.pi ^ 6 :=
    pow_lt_pow_left₀ Real.pi_gt_d4 (by norm_num) (by norm_num)
  have hscale6 : (59 / 16 : ℝ) ^ 6 < 3 * Real.pi ^ 6 := by
    nlinarith [show (59 / 16 : ℝ) ^ 6 < 3 * (3.1415 : ℝ) ^ 6 by norm_num]
  have hdiff : (13 / 3 : ℝ) < (59 / 16 - Real.pi) * d := by
    nlinarith [Real.pi_lt_d4]
  have hextra : Real.exp (-((59 / 16 - Real.pi) * d)) < (1 / 60 : ℝ) := by
    exact (Real.exp_lt_exp.mpr (by linarith)).trans exp_neg_thirteenThirds_lt_oneSixtieth
  have hbase : (59 / 16 : ℝ) ^ 6 * Real.exp (-(59 / 16 : ℝ) * d) <
      (1 / 20 : ℝ) * Real.pi ^ 6 * Real.exp (-Real.pi * d) := by
    rw [show -(59 / 16 : ℝ) * d =
        -Real.pi * d + -((59 / 16 - Real.pi) * d) by ring,
      Real.exp_add]
    nlinarith [Real.exp_pos (-Real.pi * d), Real.pi_pos]
  exact hmono.trans hbase.le

/-- Every stable atom gains the scale-local factor `1/20` from scale `59/16`. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_le_oneTwentieth_of_59Over16_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : (59 / 16 : ℝ) ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomSixthScoreMass n A B ≤
      (3 / 20 : ℝ) * Real.pi ^ 6 * thetaCuspReflectionJetTailWeight 6 (n - 2) := by
  let d := thetaCuspLikelihoodGap n
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    nlinarith
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 59 / 16)).le.trans hA
  have hB : 0 < B := by rw [hBA]; linarith
  have hB41 : (3 / 2 : ℝ) < B := by rw [hBA]; linarith
  have hA0 : 0 < A := by linarith
  have hz : (47 / 5 : ℝ) < A * d := by
    have hmul := mul_le_mul hApi hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_d2]
  have hy : 16 ≤ A * d - 9 := by
    have hmul := mul_le_mul hApi hd (by norm_num : (0 : ℝ) ≤ 8) hA0.le
    nlinarith [Real.pi_gt_d2]
  have hr0 : 0 ≤ A / B := div_nonneg hA0.le hB.le
  have hr : A / B ≤ 2 := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    linarith
  have hpointScore := thetaLikelihoodSixthScore_le_pow_six hz
  have hrayPoly := thetaLikelihoodSixthScoreRayTransformPolynomial_le_two_pow hr0 hr hy
  have hrayPoly' :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9) ≤
        2 * (A * d) ^ 6 := by
    convert hrayPoly using 1
    ring
  have hexp :
      Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d)) = Real.exp (-A * d) := by
    rw [← Real.exp_add]
    rw [hBA]
    congr 1
    ring
  have hpoint :
      thetaCuspLikelihoodAtomWeight n *
          (thetaLikelihoodSixthScore (A * d) * Real.exp (-(B * d))) ≤
        (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
    unfold thetaCuspLikelihoodAtomWeight
    calc
      _ ≤ Real.exp (-(3 / 2 : ℝ) * d) * (n : ℝ) ^ 4 *
          ((A * d) ^ 6 * Real.exp (-(B * d))) := by gcongr
      _ = _ := by
        rw [mul_pow]
        rw [show Real.exp (-(3 / 2 : ℝ) * d) * (n : ℝ) ^ 4 *
            (A ^ 6 * d ^ 6 * Real.exp (-(B * d))) =
          (n : ℝ) ^ 4 * A ^ 6 * d ^ 6 *
            (Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d))) by ring,
          hexp]
        ring
  have hray :
      thetaCuspLikelihoodRayWeight n *
          (Real.exp (-(B * d)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9)) ≤
        2 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
    have hnd : (n : ℝ) ^ 2 * d ≤ (n : ℝ) ^ 4 := by
      dsimp [d, thetaCuspLikelihoodGap]
      nlinarith [sq_nonneg (n : ℝ)]
    unfold thetaCuspLikelihoodRayWeight
    calc
      _ ≤ Real.exp (-(3 / 2 : ℝ) * d) * (3 / 2 : ℝ) * (n : ℝ) ^ 2 * d *
          (Real.exp (-(B * d)) / B * (2 * (A * d) ^ 6)) := by gcongr
      _ = (3 / B) * ((n : ℝ) ^ 2 * d) * d ^ 6 *
          (A ^ 6 * Real.exp (-A * d)) := by
        rw [mul_pow]
        rw [show Real.exp (-(3 / 2 : ℝ) * d) * (3 / 2 : ℝ) *
            (n : ℝ) ^ 2 * d *
              (Real.exp (-(B * d)) / B * (2 * (A ^ 6 * d ^ 6))) =
          (3 / B) * ((n : ℝ) ^ 2 * d) * d ^ 6 * A ^ 6 *
            (Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d))) by ring,
          hexp]
        ring
      _ ≤ 2 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
        have hthree : 3 / B < 2 := by
          apply (div_lt_iff₀ hB).2
          linarith
        gcongr
  have hscale := thetaSixthScalePowExp_le_oneTwentieth_pi_of_59Over16_le hA hd
  rw [thetaCuspLikelihoodAtomSixthScoreMass_eq n (by omega) A hB]
  change _ * (thetaLikelihoodSixthScore (A * d) * _) +
    _ * (_ / B * thetaLikelihoodSixthScoreRayTransformPolynomial
      (A / B) (A * d - 9)) ≤ _
  have hsum :
      thetaCuspLikelihoodAtomWeight n *
          (thetaLikelihoodSixthScore (A * d) * Real.exp (-(B * d))) +
        thetaCuspLikelihoodRayWeight n *
          (Real.exp (-(B * d)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9)) ≤
        3 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := by
    nlinarith
  calc
    _ ≤ 3 * (n : ℝ) ^ 4 * d ^ 6 * (A ^ 6 * Real.exp (-A * d)) := hsum
    _ ≤ 3 * (n : ℝ) ^ 4 * d ^ 6 *
        ((1 / 20 : ℝ) * Real.pi ^ 6 * Real.exp (-Real.pi * d)) := by gcongr
    _ = (3 / 20 : ℝ) * Real.pi ^ 6 *
        thetaCuspReflectionJetTailWeight 6 (n - 2) := by
      unfold thetaCuspReflectionJetTailWeight
      have hnsub : n - 2 + 2 = n := by omega
      simp only [hnsub]
      dsimp only [d, thetaCuspLikelihoodGap]
      ring

/-- Complete stable sixth-score tower is strictly below one half above scale `59/16`. -/
theorem tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_oneHalf_of_59Over16_le
    {A B : ℝ} (hA : (59 / 16 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) < 1 / 2 := by
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 59 / 16)).le.trans hA
  have hs := summable_thetaCuspLikelihoodStableAtomSixthScoreMass hApi hBA
  have hw : Summable (fun k : ℕ =>
      ((3 / 20 : ℝ) * Real.pi ^ 6) * thetaCuspReflectionJetTailWeight 6 (k + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6)).mul_left _
  have hsum :
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
        (1 / 1998 : ℝ) * Real.pi ^ 6 := by
    calc
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
          ∑' k : ℕ, ((3 / 20 : ℝ) * Real.pi ^ 6) *
            thetaCuspReflectionJetTailWeight 6 (k + 1) := by
        apply Summable.tsum_le_tsum _ hs hw
        intro k
        simpa only [show k + 3 - 2 = k + 1 by omega] using
          thetaCuspLikelihoodAtomSixthScoreMass_le_oneTwentieth_of_59Over16_le
            (n := k + 3) (by omega) hA hBA
      _ = ((3 / 20 : ℝ) * Real.pi ^ 6) *
          (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) := by
        rw [tsum_mul_left]
      _ ≤ ((3 / 20 : ℝ) * Real.pi ^ 6) * (10 / 2997 : ℝ) := by
        gcongr
        exact tsum_thetaCuspReflectionJetTailWeight_six_tail_le
      _ = (1 / 1998 : ℝ) * Real.pi ^ 6 := by ring
  have hpi2 : Real.pi ^ 2 < (987 / 100 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpow :=
    pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
  have hpi6 : Real.pi ^ 6 < (970 : ℝ) := by
    calc
      Real.pi ^ 6 = (Real.pi ^ 2) ^ 3 := by ring
      _ < (987 / 100 : ℝ) ^ 3 := hpow
      _ < 970 := by norm_num
  nlinarith

end
end RHTower
