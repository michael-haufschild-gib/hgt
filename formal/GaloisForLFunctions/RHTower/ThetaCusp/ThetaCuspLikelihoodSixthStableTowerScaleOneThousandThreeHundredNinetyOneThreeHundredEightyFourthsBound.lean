import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthStableTowerScaleTwentyNineEighthsBound

/-!
# Stable sixth tower below one half at scale 1391/384

The sharper scale comparison retains factor `519/10000`; combined with `pi^(6 : ℕ) < 962`, the
complete stable sixth-score tower remains strictly below `1/2` on the adjacent dyadic chamber.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Elementary exponential input for the scale-`1391/384` stable edge. -/
theorem exp_neg_ninetySixTwentyFifths_lt_oneHundredSeventyThreeEightThousandths :
    Real.exp (-(96 / 25 : ℝ)) < (173 / 8000 : ℝ) := by
  have hpow3 : (2.7182818283 : ℝ) ^ (3 : ℕ) < Real.exp 1 ^ (3 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h3 : (20085 / 1000 : ℝ) < Real.exp 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (20085 / 1000 : ℝ) < (2.7182818283 : ℝ) ^ (3 : ℕ)).trans hpow3
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 21 / 25) 6
  have hsmall : (231 / 100 : ℝ) < Real.exp (21 / 25) := by
    have hsum' : (231 / 100 : ℝ) <
        ∑ k ∈ Finset.range 6, (21 / 25 : ℝ) ^ k / k.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hsum'.trans_le hsum
  have hlarge : (8000 / 173 : ℝ) < Real.exp (96 / 25) := by
    rw [show (96 / 25 : ℝ) = 3 + 21 / 25 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (3 : ℝ), Real.exp_pos (21 / 25 : ℝ)]
  have hprod : Real.exp (-(96 / 25 : ℝ)) * Real.exp (96 / 25) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(96 / 25 : ℝ))]

/-- Above scale `1391/384`, stable-edge decay gains `519/10000` over frozen `pi`. -/
theorem thetaSixthScalePowExp_le_fiveHundredNineteenTenThousandths_pi_of_1391Over384_le
    {A d : ℝ} (hA : (1391 / 384 : ℝ) ≤ A) (hd : 8 ≤ d) :
    A ^ (6 : ℕ) * Real.exp (-A * d) ≤
      (519 / 10000 : ℝ) * Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d) := by
  have hd0 : 0 < d := by linarith
  have hmono := thetaSixthScalePowExp_le_of_scale_ge
    (a := (1391 / 384 : ℝ)) (A := A) (d := d) (by
      apply (div_le_iff₀ hd0).2
      nlinarith) hA hd0
  have hpi6lo : (3.1415 : ℝ) ^ (6 : ℕ) < Real.pi ^ (6 : ℕ) :=
    pow_lt_pow_left₀ Real.pi_gt_d4 (by norm_num) (by norm_num)
  have hscale6 : (1391 / 384 : ℝ) ^ (6 : ℕ) < (12 / 5 : ℝ) * Real.pi ^ (6 : ℕ) := by
    nlinarith [show (1391 / 384 : ℝ) ^ (6 : ℕ) <
      (12 / 5 : ℝ) * (3.1415 : ℝ) ^ (6 : ℕ) by norm_num]
  have hdiff : (96 / 25 : ℝ) < (1391 / 384 - Real.pi) * d := by
    nlinarith [Real.pi_lt_d4]
  have hextra : Real.exp (-((1391 / 384 - Real.pi) * d)) < (173 / 8000 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans
      exp_neg_ninetySixTwentyFifths_lt_oneHundredSeventyThreeEightThousandths
  have hbase : (1391 / 384 : ℝ) ^ (6 : ℕ) * Real.exp (-(1391 / 384 : ℝ) * d) <
      (519 / 10000 : ℝ) * Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d) := by
    rw [show -(1391 / 384 : ℝ) * d =
        -Real.pi * d + -((1391 / 384 - Real.pi) * d) by ring,
      Real.exp_add]
    nlinarith [Real.exp_pos (-Real.pi * d), Real.pi_pos]
  exact hmono.trans hbase.le

/-- Every stable atom gains the scale-local factor `519/10000`. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_le_fiveHundredNineteenTenThousandths_of_1391Over384_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : (1391 / 384 : ℝ) ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomSixthScoreMass n A B ≤
      (1557 / 10000 : ℝ) * Real.pi ^ (6 : ℕ) * thetaCuspReflectionJetTailWeight 6 (n - 2) := by
  let d := thetaCuspLikelihoodGap n
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    nlinarith
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 1391 / 384)).le.trans hA
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
  have hscale :=
    thetaSixthScalePowExp_le_fiveHundredNineteenTenThousandths_pi_of_1391Over384_le
      hA hd
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
        ((519 / 10000 : ℝ) * Real.pi ^ (6 : ℕ) * Real.exp (-Real.pi * d)) := by gcongr
    _ = (1557 / 10000 : ℝ) * Real.pi ^ (6 : ℕ) *
        thetaCuspReflectionJetTailWeight 6 (n - 2) := by
      unfold thetaCuspReflectionJetTailWeight
      have hnsub : n - 2 + 2 = n := by omega
      simp only [hnsub]
      dsimp only [d, thetaCuspLikelihoodGap]
      ring

/-- Complete stable sixth-score tower is below one half above scale `1391/384`. -/
theorem tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_oneHalf_of_1391Over384_le
    {A B : ℝ} (hA : (1391 / 384 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) < 1 / 2 := by
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 1391 / 384)).le.trans hA
  have hs := summable_thetaCuspLikelihoodStableAtomSixthScoreMass hApi hBA
  have hw : Summable (fun k : ℕ =>
      ((1557 / 10000 : ℝ) * Real.pi ^ (6 : ℕ)) * thetaCuspReflectionJetTailWeight 6 (k + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6)).mul_left _
  have hsum :
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
        (173 / 333000 : ℝ) * Real.pi ^ (6 : ℕ) := by
    calc
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
          ∑' k : ℕ, ((1557 / 10000 : ℝ) * Real.pi ^ (6 : ℕ)) *
            thetaCuspReflectionJetTailWeight 6 (k + 1) := by
        apply Summable.tsum_le_tsum _ hs hw
        intro k
        simpa only [show k + 3 - 2 = k + 1 by omega] using
          thetaCuspLikelihoodAtomSixthScoreMass_le_fiveHundredNineteenTenThousandths_of_1391Over384_le
            (n := k + 3) (by omega) hA hBA
      _ = ((1557 / 10000 : ℝ) * Real.pi ^ (6 : ℕ)) *
          (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) := by
        rw [tsum_mul_left]
      _ ≤ ((1557 / 10000 : ℝ) * Real.pi ^ (6 : ℕ)) * (10 / 2997 : ℝ) := by
        gcongr
        exact tsum_thetaCuspReflectionJetTailWeight_six_tail_le
      _ = (173 / 333000 : ℝ) * Real.pi ^ (6 : ℕ) := by ring
  have hpi2 : Real.pi ^ (2 : ℕ) < (987 / 100 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpow :=
    pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
  have hpi6 : Real.pi ^ (6 : ℕ) < (962 : ℝ) := by
    calc
      Real.pi ^ (6 : ℕ) = (Real.pi ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
      _ < (987 / 100 : ℝ) ^ (3 : ℕ) := hpow
      _ < 962 := by norm_num
  nlinarith

end

end RHTower
