import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleOneThousandThreeHundredNinetyOneThreeHundredEightyFourthsAffineBound
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodScaleLocalBellCoolingEighteenFifths

/-!
# Scale-18/5 affine upper bound for the sixth likelihood jet

The exact dominant atom is below `2959/10 - 480d`; a new scale-local comparison puts the
complete stable tower below one.  Bell inflation therefore gives the moving logarithmic
ceiling `(40096/625)(2969/10 - 480d)` on `18/5 ≤ A ≤ 1391/384`.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Elementary stable-edge exponential input. -/
theorem exp_neg_eighteenFifths_lt_oneTwentyFifth :
    Real.exp (-(18 / 5 : ℝ)) < (1 / 25 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 18 / 5) 10
  have hlarge : (25 : ℝ) < Real.exp (18 / 5) := by
    exact (show (25 : ℝ) <
        ∑ k ∈ Finset.range 10, (18 / 5 : ℝ) ^ k / k.factorial by
          norm_num [Finset.sum_range_succ, Nat.factorial]).trans_le he
  have hprod : Real.exp (-(18 / 5 : ℝ)) * Real.exp (18 / 5) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(18 / 5 : ℝ))]

/-- Above `A=18/5`, stable-edge power-exponential mass gains factor `12/125`. -/
theorem thetaSixthScalePowExp_le_twelveOneHundredTwentyFifths_pi_of_18Over5_le
    {A d : ℝ} (hA : (18 / 5 : ℝ) ≤ A) (hd : 8 ≤ d) :
    A ^ 6 * Real.exp (-A * d) ≤
      (12 / 125 : ℝ) * Real.pi ^ 6 * Real.exp (-Real.pi * d) := by
  have hd0 : 0 < d := by linarith
  have hmono := thetaSixthScalePowExp_le_of_scale_ge
    (a := (18 / 5 : ℝ)) (A := A) (d := d) (by
      apply (div_le_iff₀ hd0).2
      nlinarith) hA hd0
  have hpi6lo : (3.1415 : ℝ) ^ 6 < Real.pi ^ 6 :=
    pow_lt_pow_left₀ Real.pi_gt_d4 (by norm_num) (by norm_num)
  have hscale6 : (18 / 5 : ℝ) ^ 6 < (12 / 5 : ℝ) * Real.pi ^ 6 := by
    nlinarith [show (18 / 5 : ℝ) ^ 6 <
      (12 / 5 : ℝ) * (3.1415 : ℝ) ^ 6 by norm_num]
  have hdiff : (18 / 5 : ℝ) < (18 / 5 - Real.pi) * d := by
    nlinarith [Real.pi_lt_d4]
  have hextra : Real.exp (-((18 / 5 - Real.pi) * d)) < (1 / 25 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans exp_neg_eighteenFifths_lt_oneTwentyFifth
  have hbase : (18 / 5 : ℝ) ^ 6 * Real.exp (-(18 / 5 : ℝ) * d) <
      (12 / 125 : ℝ) * Real.pi ^ 6 * Real.exp (-Real.pi * d) := by
    rw [show -(18 / 5 : ℝ) * d =
        -Real.pi * d + -((18 / 5 - Real.pi) * d) by ring,
      Real.exp_add]
    nlinarith [Real.exp_pos (-Real.pi * d), Real.pi_pos]
  exact hmono.trans hbase.le

/-- Every stable atom gains the scale-local factor `12/125`. -/
theorem thetaCuspLikelihoodAtomSixthScoreMass_le_twelveOneHundredTwentyFifths_of_18Over5_le
    {n : ℕ} (hn : 3 ≤ n) {A B : ℝ} (hA : (18 / 5 : ℝ) ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodAtomSixthScoreMass n A B ≤
      (36 / 125 : ℝ) * Real.pi ^ 6 * thetaCuspReflectionJetTailWeight 6 (n - 2) := by
  let d := thetaCuspLikelihoodGap n
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    nlinarith
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 18 / 5)).le.trans hA
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
  have hscale :=
    thetaSixthScalePowExp_le_twelveOneHundredTwentyFifths_pi_of_18Over5_le hA hd
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
        ((12 / 125 : ℝ) * Real.pi ^ 6 * Real.exp (-Real.pi * d)) := by gcongr
    _ = (36 / 125 : ℝ) * Real.pi ^ 6 *
        thetaCuspReflectionJetTailWeight 6 (n - 2) := by
      unfold thetaCuspReflectionJetTailWeight
      have hnsub : n - 2 + 2 = n := by omega
      simp only [hnsub]
      dsimp only [d, thetaCuspLikelihoodGap]
      ring

/-- Complete stable sixth-score tower is below one above scale `18/5`. -/
theorem tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_one_of_18Over5_le
    {A B : ℝ} (hA : (18 / 5 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) < 1 := by
  have hApi : Real.pi ≤ A :=
    (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 18 / 5)).le.trans hA
  have hs := summable_thetaCuspLikelihoodStableAtomSixthScoreMass hApi hBA
  have hw : Summable (fun k : ℕ =>
      ((36 / 125 : ℝ) * Real.pi ^ 6) * thetaCuspReflectionJetTailWeight 6 (k + 1)) :=
    ((summable_nat_add_iff 1).2 (summable_thetaCuspReflectionJetTailWeight 6)).mul_left _
  have hsum :
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
        (8 / 8325 : ℝ) * Real.pi ^ 6 := by
    calc
      (∑' k : ℕ, thetaCuspLikelihoodAtomSixthScoreMass (k + 3) A B) ≤
          ∑' k : ℕ, ((36 / 125 : ℝ) * Real.pi ^ 6) *
            thetaCuspReflectionJetTailWeight 6 (k + 1) := by
        apply Summable.tsum_le_tsum _ hs hw
        intro k
        simpa only [show k + 3 - 2 = k + 1 by omega] using
          thetaCuspLikelihoodAtomSixthScoreMass_le_twelveOneHundredTwentyFifths_of_18Over5_le
            (n := k + 3) (by omega) hA hBA
      _ = ((36 / 125 : ℝ) * Real.pi ^ 6) *
          (∑' k : ℕ, thetaCuspReflectionJetTailWeight 6 (k + 1)) := by
        rw [tsum_mul_left]
      _ ≤ ((36 / 125 : ℝ) * Real.pi ^ 6) * (10 / 2997 : ℝ) := by
        gcongr
        exact tsum_thetaCuspReflectionJetTailWeight_six_tail_le
      _ = (8 / 8325 : ℝ) * Real.pi ^ 6 := by ring
  have hpi2 : Real.pi ^ 2 < (987 / 100 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpow := pow_lt_pow_left₀ hpi2 (sq_nonneg Real.pi) (by norm_num : (3 : ℕ) ≠ 0)
  have hpi6 : Real.pi ^ 6 < (962 : ℝ) := by
    calc
      Real.pi ^ 6 = (Real.pi ^ 2) ^ 3 := by ring
      _ < (987 / 100 : ℝ) ^ 3 := hpow
      _ < 962 := by norm_num
  nlinarith

/-- Exact rational score factor after extracting `exp(-3A)` at scale `18/5`. -/
def thetaCuspLikelihoodSixthScale18Over5DominantPolynomial (d : ℝ) : ℝ :=
  16 * thetaLikelihoodSixthScoreShift (9 / 5 + 3 * d) +
    18 * (1 / (21 / 10 + d)) *
      thetaLikelihoodSixthScoreRayTransformPolynomial
        ((18 / 5 + d) / (21 / 10 + d)) (9 / 5 + 3 * d)

/-- Sharp rational upper enclosure for `exp (-54/5)`. -/
theorem exp_neg_fiftyFourFifths_lt_oneOverFortyNineThousand :
    Real.exp (-(54 / 5 : ℝ)) < (1 / 49000 : ℝ) := by
  have hpow : Real.exp (-1) ^ 10 < (0.3678794412 : ℝ) ^ 10 :=
    pow_lt_pow_left₀ Real.exp_neg_one_lt_d9 (Real.exp_pos (-1)).le (by norm_num)
  have hfrac : Real.exp (-(4 / 5 : ℝ)) < (899 / 2000 : ℝ) := by
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) 8
    have hb : (2000 / 899 : ℝ) < Real.exp (4 / 5) := by
      calc
        (2000 / 899 : ℝ) <
            ∑ k ∈ Finset.range 8, (4 / 5 : ℝ) ^ k / k.factorial := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
        _ ≤ Real.exp (4 / 5) := he
    have hprod : Real.exp (-(4 / 5 : ℝ)) * Real.exp (4 / 5 : ℝ) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-(4 / 5 : ℝ))]
  rw [show (-(54 / 5 : ℝ)) = -10 + -(4 / 5 : ℝ) by norm_num,
    Real.exp_add,
    show Real.exp (-10) = Real.exp (-1) ^ 10 by
      rw [show (-10 : ℝ) = (10 : ℕ) * (-1 : ℝ) by norm_num,
        Real.exp_nat_mul]]
  nlinarith [Real.exp_pos (-1), Real.exp_pos (-(4 / 5 : ℝ)),
    show (0.3678794412 : ℝ) ^ 10 * (899 / 2000 : ℝ) < 1 / 49000 by norm_num]

set_option maxHeartbeats 6000000 in
/-- Cleared degree-fifteen certificate for the dominant affine budget. -/
theorem thetaCuspLikelihoodSixthScale18Over5DominantPolynomial_lt
    {d : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 43 / 1920) :
    (1 / 49000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) *
        thetaCuspLikelihoodSixthScale18Over5DominantPolynomial d <
      2959 / 10 - 480 * d := by
  have hB : 0 < 21 / 10 + d := by linarith
  have hmul : (21 / 10 + d) ^ 7 *
      ((1 / 49000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) *
        thetaCuspLikelihoodSixthScale18Over5DominantPolynomial d) <
      (21 / 10 + d) ^ 7 * (2959 / 10 - 480 * d) := by
    dsimp [thetaCuspLikelihoodSixthScale18Over5DominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    field_simp [hB.ne']
    ring_nf
    rw [← sub_pos]
    ring_nf
    have hd2 : d ^ 2 ≤ (43 / 1920 : ℝ) ^ 2 := pow_le_pow_left₀ hd hdhi 2
    have hd3 : d ^ 3 ≤ (43 / 1920 : ℝ) ^ 3 := pow_le_pow_left₀ hd hdhi 3
    have hd4 : d ^ 4 ≤ (43 / 1920 : ℝ) ^ 4 := pow_le_pow_left₀ hd hdhi 4
    have hd5 : d ^ 5 ≤ (43 / 1920 : ℝ) ^ 5 := pow_le_pow_left₀ hd hdhi 5
    have hd6 : d ^ 6 ≤ (43 / 1920 : ℝ) ^ 6 := pow_le_pow_left₀ hd hdhi 6
    have hd7 : d ^ 7 ≤ (43 / 1920 : ℝ) ^ 7 := pow_le_pow_left₀ hd hdhi 7
    have hd8 : d ^ 8 ≤ (43 / 1920 : ℝ) ^ 8 := pow_le_pow_left₀ hd hdhi 8
    have hd9 : d ^ 9 ≤ (43 / 1920 : ℝ) ^ 9 := pow_le_pow_left₀ hd hdhi 9
    have hd10 : d ^ 10 ≤ (43 / 1920 : ℝ) ^ 10 := pow_le_pow_left₀ hd hdhi 10
    have hd11 : d ^ 11 ≤ (43 / 1920 : ℝ) ^ 11 := pow_le_pow_left₀ hd hdhi 11
    have hd12 : d ^ 12 ≤ (43 / 1920 : ℝ) ^ 12 := pow_le_pow_left₀ hd hdhi 12
    have hd13 : d ^ 13 ≤ (43 / 1920 : ℝ) ^ 13 := pow_le_pow_left₀ hd hdhi 13
    have hd14 : d ^ 14 ≤ (43 / 1920 : ℝ) ^ 14 := pow_le_pow_left₀ hd hdhi 14
    have hd15 : d ^ 15 ≤ (43 / 1920 : ℝ) ^ 15 := pow_le_pow_left₀ hd hdhi 15
    norm_num at hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 hd13 hd14 hd15 ⊢
    nlinarith
  nlinarith [pow_pos hB 7]

/-- Dominant first atom-ray sixth mass obeys `2959/10 - 480d`. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale18Over5_affine
    (A : ℝ) {B : ℝ} (hAlo : (18 / 5 : ℝ) ≤ A) (hAhi : A ≤ 1391 / 384)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B <
      2959 / 10 - 480 * (A - 18 / 5) := by
  have hB : 0 < B := by rw [hBA]; linarith
  let d := A - 18 / 5
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hdhi : d ≤ 43 / 1920 := by dsimp only [d]; linarith
  have hAeq : A = 18 / 5 + d := by dsimp only [d]; ring
  have hBeq : B = 21 / 10 + d := by rw [hBA, hAeq]; ring
  have hy : 3 * A - 9 = 9 / 5 + 3 * d := by rw [hAeq]; ring
  have hextract :
      Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) = Real.exp (-3 * A) := by
    rw [← Real.exp_add]
    congr 1
    rw [hBA]
    ring
  have hmassEq : thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      Real.exp (-3 * A) * thetaCuspLikelihoodSixthScale18Over5DominantPolynomial d := by
    rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB,
      thetaLikelihoodSixthScore_eq_shiftNine, hy]
    rw [show Real.exp (-(3 * B)) / B = Real.exp (-(3 * B)) * (1 / B) by ring]
    rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScoreShift (9 / 5 + 3 * d) * Real.exp (-(3 * B))) +
        18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (1 / B) *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (9 / 5 + 3 * d)) =
        (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B))) *
          (16 * thetaLikelihoodSixthScoreShift (9 / 5 + 3 * d) +
            18 * (1 / B) * thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (9 / 5 + 3 * d)) by ring]
    rw [hextract, hAeq, hBeq]
    rfl
  have hexpd : Real.exp (-(3 * d)) ≤ 1 - 3 * d + (3 * d) ^ 2 / 2 :=
    exp_neg_le_quadratic (by positivity)
  have hExp : Real.exp (-3 * A) <
      (1 / 49000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) := by
    calc
      Real.exp (-3 * A) = Real.exp (-(54 / 5 : ℝ)) * Real.exp (-(3 * d)) := by
        rw [← Real.exp_add, hAeq]
        congr 1
        ring
      _ < (1 / 49000 : ℝ) * Real.exp (-(3 * d)) := by
        gcongr
        exact exp_neg_fiftyFourFifths_lt_oneOverFortyNineThousand
      _ ≤ (1 / 49000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2) := by gcongr
  have hpolypos : 0 < thetaCuspLikelihoodSixthScale18Over5DominantPolynomial d := by
    have hBd : 0 < 21 / 10 + d := by linarith
    dsimp [thetaCuspLikelihoodSixthScale18Over5DominantPolynomial,
      thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    field_simp [hBd.ne']
    ring_nf
    positivity
  rw [hmassEq]
  calc
    _ < ((1 / 49000 : ℝ) * (1 - 3 * d + (3 * d) ^ 2 / 2)) *
        thetaCuspLikelihoodSixthScale18Over5DominantPolynomial d := by gcongr
    _ < 2959 / 10 - 480 * d := by
      simpa only [mul_assoc] using
        thetaCuspLikelihoodSixthScale18Over5DominantPolynomial_lt hd hdhi
    _ = 2959 / 10 - 480 * (A - 18 / 5) := by rfl

/-- Dominant plus stable sixth-score mass is below `2969/10 - 480d`. -/
theorem integral_thetaLikelihoodSixthScore_lt_scale18Over5_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (18 / 5 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore (thetaCuspSingleAtomReflectionScale 1 x * t) *
          Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) <
      2969 / 10 - 480 * (thetaCuspSingleAtomReflectionScale 1 x - 18 / 5) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hBA : B = A - 3 / 2 := by
    simpa only [A, B] using thetaCuspSingleAtomScale_likelihoodCoordinate x
  have hd := thetaCuspLikelihoodDominantAtomSixthScoreMass_lt_scale18Over5_affine
    A (by simpa only [A] using hAlo) (by simpa only [A] using hAhi) hBA
  have hs := tsum_thetaCuspLikelihoodStableAtomSixthScoreMass_lt_one_of_18Over5_le
    (by simpa only [A] using hAlo) hBA
  rw [thetaCuspLikelihoodSixthScoreIntegral_eq_dominant_add_stable hx]
  dsimp only [A, B] at hd hs ⊢
  nlinarith

/-- Affine logarithmic sixth-jet ceiling on the scale-`18/5` chamber. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale18Over5_affine
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (18 / 5 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (40096 / 625 : ℝ) *
        (2969 / 10 - 480 * (thetaCuspSingleAtomReflectionScale 1 x - 18 / 5)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let massBudget := 2969 / 10 - 480 * (A - 18 / 5)
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hPone : 1 ≤ P := by
    have hzero := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
    change 1 ≤ thetaCuspLikelihoodPartition B
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB]
    linarith
  have hbudget : 0 < massBudget := by dsimp only [massBudget, A]; linarith
  have hscore :
      (∫ t : ℝ, thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) < massBudget := by
    simpa only [A, B, massBudget] using
      integral_thetaLikelihoodSixthScore_lt_scale18Over5_affine hx hAlo hAhi
  have hordinary : thetaCuspLikelihoodSourceOrdinaryJetSix x < 64 * massBudget := by
    have hordinaryPos := thetaCuspLikelihoodSourceOrdinaryJetSix_pos hx
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
    rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx] at hordinaryPos
    have hcoeff : 0 < 64 / P := div_pos (by norm_num) hP
    have hcoeffUpper : 64 / P ≤ 64 := by
      apply (div_le_iff₀ hP).2
      nlinarith
    have hmass0 : 0 < (∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
      dsimp only [A, B] at hordinaryPos ⊢
      nlinarith
    dsimp only [A, B] at hscore ⊢
    nlinarith [mul_lt_mul_of_pos_left hscore hcoeff,
      mul_le_mul_of_nonneg_right hcoeffUpper hmass0.le]
  have hlog :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_fiveThousandTwelveFiveThousandths_ordinary_of_18Over5_le
      hx hAlo
  dsimp only [massBudget, A] at hordinary ⊢
  nlinarith

/-- Weight-coordinate form of the scale-`18/5` sixth ceiling. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale18Over5_affine_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hAlo : (18 / 5 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hAhi : thetaCuspSingleAtomReflectionScale 1 x ≤ 1391 / 384) :
    thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (40096 / 625 : ℝ) *
        (13049 / 10 - 480 * thetaCuspBornWittenWeight 1 x) := by
  have hscale : thetaCuspSingleAtomReflectionScale 1 x =
      thetaCuspBornWittenWeight 1 x + 3 / 2 := by
    dsimp only [thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have h := thetaCuspLikelihoodSourceLogPartitionJetSix_lt_scale18Over5_affine
    hx hAlo hAhi
  rw [hscale] at h
  convert h using 1
  all_goals ring

end

end RHTower
