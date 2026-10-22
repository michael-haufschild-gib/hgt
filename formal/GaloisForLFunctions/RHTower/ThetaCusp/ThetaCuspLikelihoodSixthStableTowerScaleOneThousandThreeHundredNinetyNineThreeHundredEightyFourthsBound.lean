import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthStableTowerScaleOneHundredSeventyFiveFortyEighthsBound

/-!
# Scale-1399/384 half-unit bound for the stable sixth-score tower

At the new scale edge, eight units of spectral support still create more than four units of
additional exponential decay over the frozen `pi` envelope.  The exact sixth-power ratio remains
below `13/5`, preserving the `1/20` atom factor and complete stable-tower bound `< 1/2`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Above `1399/384`, stable-edge scale decay gains `1/20` over the frozen `pi` envelope. -/
theorem thetaSixthScalePowExp_le_oneTwentieth_pi_of_1399Over384_le
    {A d : ℝ} (hA : (1399 / 384 : ℝ) ≤ A) (hd : 8 ≤ d) :
    A ^ (6 : ℕ) * Real.exp (-A * d) ≤
      (1 / 20 : ℝ) * Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d) := by
  have hd0 : 0 < d := by linarith
  have hmono := thetaSixthScalePowExp_le_of_scale_ge
    (a := (1399 / 384 : ℝ)) (A := A) (d := d) (by
      apply (div_le_iff₀ hd0).2
      nlinarith) hA hd0
  have hpi6lo : (3.1415 : ℝ) ^ (6 : ℕ) < Real.pi ^ (6 : ℕ) :=
    pow_lt_pow_left₀ Real.pi_gt_d4 (by norm_num) (by norm_num)
  have hscale6 : (1399 / 384 : ℝ) ^ (6 : ℕ) < (13 / 5 : ℝ) * Real.pi ^ (6 : ℕ) := by
    nlinarith [show (1399 / 384 : ℝ) ^ (6 : ℕ) <
      (13 / 5 : ℝ) * (3.1415 : ℝ) ^ (6 : ℕ) by norm_num]
  have hdiff : (4 : ℝ) < (1399 / 384 - Real.pi) * d := by
    nlinarith [Real.pi_lt_d4]
  have hextra : Real.exp (-((1399 / 384 - Real.pi) * d)) < (1 / 54 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans
      exp_neg_four_lt_oneFiftyFourth_scale175Over48
  have hbase : (1399 / 384 : ℝ) ^ (6 : ℕ) * Real.exp (-(1399 / 384 : ℝ) * d) <
      (1 / 20 : ℝ) * Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d) := by
    rw [show -(1399 / 384 : ℝ) * d =
        -Real.pi * d + -((1399 / 384 - Real.pi) * d) by ring,
      Real.exp_add]
    nlinarith [Real.exp_pos (-Real.pi * d), Real.pi_pos]
  exact hmono.trans hbase.le

/-- Every stable atom gains the scale-local factor `1/20` from scale `1399/384`. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_le_oneTwentieth_of_1399Over384_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : (1399 / 384 : ℝ) ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomSixthScoreMass n A B ≤
      (3 / 20 : ℝ) * Real.pi ^ (6 : ℕ) * thetaCuspReflectionJetTailWeight 6 (n - 2) := by
  let d := thetaCuspLikelihoodGap n
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    nlinarith
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 1399 / 384)).le.trans hA
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
        2 * (A * d) ^ (6 : ℕ) := by
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
        (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) * (A ^ (6 : ℕ) * Real.exp (-A * d)) := by
    unfold thetaCuspLikelihoodAtomWeight
    calc
      _ ≤ Real.exp (-(3 / 2 : ℝ) * d) * (n : ℝ) ^ (4 : ℕ) *
          ((A * d) ^ (6 : ℕ) * Real.exp (-(B * d))) := by gcongr
      _ = _ := by
        rw [mul_pow]
        rw [show Real.exp (-(3 / 2 : ℝ) * d) * (n : ℝ) ^ (4 : ℕ) *
            (A ^ (6 : ℕ) * d ^ (6 : ℕ) * Real.exp (-(B * d))) =
          (n : ℝ) ^ (4 : ℕ) * A ^ (6 : ℕ) * d ^ (6 : ℕ) *
            (Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d))) by ring,
          hexp]
        ring
  have hray :
      thetaCuspLikelihoodRayWeight n *
          (Real.exp (-(B * d)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9)) ≤
        2 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) * (A ^ (6 : ℕ) * Real.exp (-A * d)) := by
    have hnd : (n : ℝ) ^ (2 : ℕ) * d ≤ (n : ℝ) ^ (4 : ℕ) := by
      dsimp [d, thetaCuspLikelihoodGap]
      nlinarith [sq_nonneg (n : ℝ)]
    unfold thetaCuspLikelihoodRayWeight
    calc
      _ ≤ Real.exp (-(3 / 2 : ℝ) * d) * (3 / 2 : ℝ) * (n : ℝ) ^ (2 : ℕ) * d *
          (Real.exp (-(B * d)) / B * (2 * (A * d) ^ (6 : ℕ))) := by gcongr
      _ = (3 / B) * ((n : ℝ) ^ (2 : ℕ) * d) * d ^ (6 : ℕ) *
          (A ^ (6 : ℕ) * Real.exp (-A * d)) := by
        rw [mul_pow]
        rw [show Real.exp (-(3 / 2 : ℝ) * d) * (3 / 2 : ℝ) *
            (n : ℝ) ^ (2 : ℕ) * d *
              (Real.exp (-(B * d)) / B * (2 * (A ^ (6 : ℕ) * d ^ (6 : ℕ)))) =
          (3 / B) * ((n : ℝ) ^ (2 : ℕ) * d) * d ^ (6 : ℕ) * A ^ (6 : ℕ) *
            (Real.exp (-(3 / 2 : ℝ) * d) * Real.exp (-(B * d))) by ring,
          hexp]
        ring
      _ ≤ 2 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) * (A ^ (6 : ℕ) * Real.exp (-A * d)) := by
        have hthree : 3 / B < 2 := by
          apply (div_lt_iff₀ hB).2
          linarith
        gcongr
  have hscale := thetaSixthScalePowExp_le_oneTwentieth_pi_of_1399Over384_le hA hd
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
        3 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) * (A ^ (6 : ℕ) * Real.exp (-A * d)) := by
    nlinarith
  calc
    _ ≤ 3 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) * (A ^ (6 : ℕ) * Real.exp (-A * d)) := hsum
    _ ≤ 3 * (n : ℝ) ^ (4 : ℕ) * d ^ (6 : ℕ) *
        ((1 / 20 : ℝ) * Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d)) := by gcongr
    _ = (3 / 20 : ℝ) * Real.pi ^ (6 : ℕ) *
        thetaCuspReflectionJetTailWeight 6 (n - 2) := by
      unfold thetaCuspReflectionJetTailWeight
      have hnsub : n - 2 + 2 = n := by omega
      simp only [hnsub]
      dsimp only [d, thetaCuspLikelihoodGap]
      ring

/-- Complete stable sixth-score tower is below one half above scale `1399/384`. -/
theorem tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_oneHalf_of_1399Over384_le
    {A B : ℝ} (hA : (1399 / 384 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) < 1 / 2 := by
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 1399 / 384)).le.trans hA
  have hs := summable_thetaCuspLikelihoodStableAtomSixthScoreMass hApi hBA
  have hw : Summable (fun k : ℕ =>
      ((3 / 20 : ℝ) * Real.pi ^ (6 : ℕ)) * thetaCuspReflectionJetTailWeight 6 (k + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6)).mul_left _
  have hsum :
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
        (1 / 1998 : ℝ) * Real.pi ^ (6 : ℕ) := by
    calc
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
          ∑' k : ℕ, ((3 / 20 : ℝ) * Real.pi ^ (6 : ℕ)) *
            thetaCuspReflectionJetTailWeight 6 (k + 1) := by
        apply Summable.tsum_le_tsum _ hs hw
        intro k
        simpa only [show k + 3 - 2 = k + 1 by omega] using
          thetaCuspLikelihoodAtomSixthScoreMass_le_oneTwentieth_of_1399Over384_le
            (n := k + 3) (by omega) hA hBA
      _ = ((3 / 20 : ℝ) * Real.pi ^ (6 : ℕ)) *
          (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) := by
        rw [tsum_mul_left]
      _ ≤ ((3 / 20 : ℝ) * Real.pi ^ (6 : ℕ)) * (10 / 2997 : ℝ) := by
        gcongr
        exact tsum_thetaCuspReflectionJetTailWeight_six_tail_le
      _ = (1 / 1998 : ℝ) * Real.pi ^ (6 : ℕ) := by ring
  have hpi2 : Real.pi ^ (2 : ℕ) < (987 / 100 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpow := pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
  have hpi6 : Real.pi ^ (6 : ℕ) < (970 : ℝ) := by
    calc
      Real.pi ^ (6 : ℕ) = (Real.pi ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
      _ < (987 / 100 : ℝ) ^ (3 : ℕ) := hpow
      _ < 970 := by norm_num
  nlinarith

end

end RHTower
