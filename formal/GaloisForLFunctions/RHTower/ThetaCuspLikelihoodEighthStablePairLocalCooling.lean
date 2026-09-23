import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthFockSector

/-!
# Scale-local cooling of nondominant eighth pair sectors

Retaining the full `A - pi` gap in every stable eighth atom reduces the complete
nondominant pair charge from the global `376399/1999` bound to `53051/9995`
above scale `1389/384`.
-/

namespace RHTower

noncomputable section

/-- Elementary exponential certificate for the scale-local stable edge. -/
theorem exp_neg_nineteenFifths_lt_twentyThreeThousandths :
    Real.exp (-(19 / 5 : ℝ)) < (23 / 1000 : ℝ) := by
  have hpow3 : (2.7182818283 : ℝ) ^ (3 : ℕ) < Real.exp 1 ^ (3 : ℕ) :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h3 : (20085 / 1000 : ℝ) < Real.exp 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (20085 / 1000 : ℝ) < (2.7182818283 : ℝ) ^ (3 : ℕ)).trans hpow3
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) 6
  have hsmall : (217 / 100 : ℝ) < Real.exp (4 / 5) := by
    have hsum' : (217 / 100 : ℝ) <
        ∑ k ∈ Finset.range 6, (4 / 5 : ℝ) ^ k / k.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hsum'.trans_le hsum
  have hlarge : (1000 / 23 : ℝ) < Real.exp (19 / 5) := by
    rw [show (19 / 5 : ℝ) = 3 + 4 / 5 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (3 : ℝ), Real.exp_pos (4 / 5 : ℝ)]
  have hprod : Real.exp (-(19 / 5 : ℝ)) * Real.exp (19 / 5) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(19 / 5 : ℝ))]

/-- Every stable eighth Gaussian term retains a factor `23/1000` above scale `1389/384`. -/
theorem thetaCuspLikelihoodStableEighthTailTerm_le_twentyThreeThousandths_of_1389Over384_le
    {A : ℝ} (hA : (1389 / 384 : ℝ) ≤ A) (k : ℕ) :
    ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
        Real.exp (-(A * thetaCuspLikelihoodGap (k + 3))) ≤
      (23 / 1000 : ℝ) * thetaCuspReflectionJetTailWeight 8 (k + 1) := by
  let d := thetaCuspLikelihoodGap (k + 3)
  have hd : 8 ≤ d := by
    dsimp [d, thetaCuspLikelihoodGap]
    have hk : (0 : ℝ) ≤ k := by positivity
    push_cast
    nlinarith
  have hApi : Real.pi ≤ A := by
    nlinarith [Real.pi_lt_d4]
  have hdiff : (19 / 5 : ℝ) < (A - Real.pi) * d := by
    nlinarith [Real.pi_lt_d4]
  have hextra : Real.exp (-((A - Real.pi) * d)) < (23 / 1000 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith)).trans exp_neg_nineteenFifths_lt_twentyThreeThousandths
  have hcoef : 0 < ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * d ^ (8 : ℕ) := by positivity
  have hpiExp : 0 < Real.exp (-(Real.pi * d)) := Real.exp_pos _
  have hexpEq : Real.exp (-(A * d)) =
      Real.exp (-(Real.pi * d)) * Real.exp (-((A - Real.pi) * d)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htailEq : thetaCuspReflectionJetTailWeight 8 (k + 1) =
      ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * d ^ (8 : ℕ) * Real.exp (-(Real.pi * d)) := by
    unfold thetaCuspReflectionJetTailWeight
    simp only [show k + 1 + 2 = k + 3 by omega]
    dsimp [d, thetaCuspLikelihoodGap]
    ring
  rw [htailEq]
  change ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * d ^ (8 : ℕ) * Real.exp (-(A * d)) ≤
    (23 / 1000 : ℝ) *
      (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * d ^ (8 : ℕ) * Real.exp (-(Real.pi * d)))
  rw [hexpEq]
  have hscaled := mul_lt_mul_of_pos_left hextra hpiExp
  have hscaledCoef := mul_lt_mul_of_pos_left hscaled hcoef
  nlinarith

/-- Complete stable eighth Gaussian tail is at most `23/19990` above scale `1389/384`. -/
theorem thetaCuspLikelihoodStableEighthTail_le_twentyThreeOverNineteenThousandNineHundredNinety_of_1389Over384_le
    {A : ℝ} (hA : (1389 / 384 : ℝ) ≤ A) :
    thetaCuspLikelihoodStableEighthTail A ≤ (23 / 19990 : ℝ) := by
  have hApi : Real.pi ≤ A := by nlinarith [Real.pi_lt_d4]
  have hs := summable_thetaCuspLikelihoodStableEighthTail hApi
  have hw : Summable (fun k : ℕ =>
      (23 / 1000 : ℝ) * thetaCuspReflectionJetTailWeight 8 (k + 1)) :=
    ((summable_nat_add_iff 1).2
      (summable_thetaCuspReflectionJetTailWeight 8)).mul_left _
  unfold thetaCuspLikelihoodStableEighthTail
  calc
    (∑' k : ℕ, ((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
        Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) ≤
      ∑' k : ℕ, (23 / 1000 : ℝ) *
        thetaCuspReflectionJetTailWeight 8 (k + 1) :=
      Summable.tsum_le_tsum
        (thetaCuspLikelihoodStableEighthTailTerm_le_twentyThreeThousandths_of_1389Over384_le hA)
        hs hw
    _ = (23 / 1000 : ℝ) *
        (∑' k : ℕ, thetaCuspReflectionJetTailWeight 8 (k + 1)) := by
      rw [tsum_mul_left]
    _ ≤ (23 / 1000 : ℝ) * (100 / 1999 : ℝ) := by
      gcongr
      exact tsum_thetaCuspReflectionJetTailWeight_eight_tail_le_sharp
    _ = (23 / 19990 : ℝ) := by ring

/-- One ordered dominant-stable pair costs at most `21528/9995` dominant units locally. -/
theorem thetaCuspLikelihoodDominantStablePairEighthTail_le_local_of_1389Over384_le
    {A B : ℝ} (hA : (1389 / 384 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantStablePairEighthTail A B ≤
      (21528 / 9995 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
  have hApi : Real.pi ≤ A := by nlinarith [Real.pi_lt_d4]
  have hs := summable_thetaCuspLikelihoodDominantStablePairEighthScoreMass hApi hBA
  have hw := (summable_thetaCuspLikelihoodStableEighthTail hApi).mul_left
    (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)))
  have htail :=
    thetaCuspLikelihoodStableEighthTail_le_twentyThreeOverNineteenThousandNineHundredNinety_of_1389Over384_le
      hA
  unfold thetaCuspLikelihoodDominantStablePairEighthTail
  calc
    (∑' k : ℕ, thetaCuspLikelihoodAtomPairEighthScoreMass 2 (k + 3) A B) ≤
        ∑' k : ℕ, 1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A)) *
          (((k + 3 : ℕ) : ℝ) ^ (4 : ℕ) * thetaCuspLikelihoodGap (k + 3) ^ (8 : ℕ) *
            Real.exp (-(A * thetaCuspLikelihoodGap (k + 3)))) :=
      Summable.tsum_le_tsum
        (fun k => thetaCuspLikelihoodDominantStablePairEighthScoreMass_le k hApi hBA)
        hs hw
    _ = (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A))) *
        thetaCuspLikelihoodStableEighthTail A := by
      unfold thetaCuspLikelihoodStableEighthTail
      rw [tsum_mul_left]
    _ ≤ (1872 * A ^ (8 : ℕ) * Real.exp (-(3 * A))) * (23 / 19990 : ℝ) := by gcongr
    _ = (21528 / 9995 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by ring

/-- Complete nondominant grade-two sector costs at most `53051/9995` dominant units locally. -/
theorem thetaCuspLikelihoodNonDominantPairEighthTail_le_local_of_1389Over384_le
    {A B : ℝ} (hA : (1389 / 384 : ℝ) ≤ A) (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodNonDominantPairEighthTail A B ≤
      (53051 / 9995 : ℝ) * A ^ (8 : ℕ) * Real.exp (-(3 * A)) := by
  have hApi : Real.pi ≤ A := by nlinarith [Real.pi_lt_d4]
  have hmixed := thetaCuspLikelihoodDominantStablePairEighthTail_le_local_of_1389Over384_le
    hA hBA
  have hstable := thetaCuspLikelihoodStableStablePairEighthTail_le hApi hBA
  unfold thetaCuspLikelihoodNonDominantPairEighthTail
  nlinarith

end

end RHTower
