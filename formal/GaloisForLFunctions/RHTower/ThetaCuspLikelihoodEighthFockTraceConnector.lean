import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthFockSector

/-!
# Eighth Fock reserve lands in the literal ordinary source trace

The completed even-Fock reserve is not only positive.  It lies strictly below the normalized
ordinary eighth derivative of the actual higher-theta likelihood partition.  This isolates the
remaining connector sharply: only logarithmic resummation, not spectral normalization or source
coordinate scaling, remains.
-/

namespace RHTower

noncomputable section

/-- Complete ordered grade-two mass is strictly positive. -/
theorem thetaCuspLikelihoodEighthPairSectorMass_pos
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    0 < thetaCuspLikelihoodEighthPairSectorMass A B := by
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hApi hBA
  have hdominant : 0 < thetaCuspLikelihoodEighthDominantPairMass A := by
    unfold thetaCuspLikelihoodEighthDominantPairMass
    exact mul_pos (Real.exp_pos _) (thetaCuspLikelihoodEighthDominantPairCore_pos hApi)
  have hmixed : 0 ≤ thetaCuspLikelihoodDominantStablePairEighthTail A B := by
    unfold thetaCuspLikelihoodDominantStablePairEighthTail
    exact tsum_nonneg fun k =>
      thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
        (by norm_num) (by omega) (Or.inr (by omega)) hA hBA
  have hstable : 0 ≤ thetaCuspLikelihoodStableStablePairEighthTail A B := by
    unfold thetaCuspLikelihoodStableStablePairEighthTail
    exact tsum_nonneg fun p =>
      thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
        (by omega) (by omega) (Or.inl (by omega)) hA hBA
  unfold thetaCuspLikelihoodEighthPairSectorMass
    thetaCuspLikelihoodNonDominantPairEighthTail
  rw [htwo]
  nlinarith

/-- Higher-even Fock loss is nonnegative. -/
theorem thetaCuspLikelihoodEighthHigherEvenFockLoss_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspLikelihoodEighthHigherEvenFockLoss x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have htail : 0 ≤ thetaCuspLikelihoodEighthHigherEvenSectorTail r := by
    unfold thetaCuspLikelihoodEighthHigherEvenSectorTail
    exact tsum_nonneg fun k => by positivity
  have hmass : 0 ≤
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthMonomialMass (k + 2) A B := by
    apply tsum_nonneg
    intro k
    unfold thetaCuspLikelihoodAtomEighthMonomialMass
    apply MeasureTheory.integral_nonneg
    intro t
    positivity
  unfold thetaCuspLikelihoodEighthHigherEvenFockLoss
  dsimp only [A, B, r]
  positivity

/-- Positive completed Fock reserve lies below its dominant one-particle source mass. -/
theorem thetaCuspLikelihoodEighthFockOddWeight_lt_dominantSingleMass
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthFockOddWeight x <
      thetaCuspLikelihoodEighthDominantSingleMass
        (thetaCuspSingleAtomReflectionScale 1 x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ (2 : ℕ) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hpair := thetaCuspLikelihoodEighthPairSectorMass_pos hA hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_nonneg hx
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  nlinarith

/-- Coefficient-faithful ordinary landing of the completed eighth Fock reserve. -/
theorem thetaCuspLikelihoodEighthFockOddWeight_lt_sourceOrdinaryJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthFockOddWeight x <
      thetaCuspLikelihoodSourceOrdinaryJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  let r := thetaCuspHigherLikelihoodSpectralResponse B
  let total := ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 2) A B
  have hA : Real.pi ≤ A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    nlinarith [Real.pi_pos]
  have hApi : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B]
    unfold thetaCuspLikelihoodCoordinate thetaCuspSingleAtomReflectionScale
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ (2 : ℕ) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    rw [← thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
    exact thetaCuspHigherLikelihoodSpectralMoment_nonneg 0
  have hr : 399 * r < 1 := by
    simpa only [B, r] using
      three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  have hPeq : P = 1 + r := by
    dsimp only [P, r]
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB,
      thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]
  have hPtwo : P < 2 := by rw [hPeq]; nlinarith
  have hfactor : 1 < 256 / P := by
    apply (lt_div_iff₀ hP).2
    nlinarith
  have hs := summable_thetaCuspLikelihoodAtomEighthScoreMass A hB
  have hstable : 0 ≤
      ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 3) A B := by
    exact tsum_nonneg fun k =>
      (thetaCuspLikelihoodStableAtomEighthScoreMass_pos
        (n := k + 3) (by omega) hA hBA).le
  have htotalSplit : total =
      thetaCuspLikelihoodAtomEighthScoreMass 2 A B +
        ∑' k : ℕ, thetaCuspLikelihoodAtomEighthScoreMass (k + 3) A B := by
    dsimp only [total]
    simpa only [Nat.add_assoc] using hs.tsum_eq_zero_add
  have hdominantEq :=
    thetaCuspLikelihoodEighthDominantSingleMass_eq_atomScoreMass hApi hBA
  have hdominantPos : 0 < thetaCuspLikelihoodEighthDominantSingleMass A := by
    unfold thetaCuspLikelihoodEighthDominantSingleMass
    exact mul_pos (Real.exp_pos _) (thetaCuspLikelihoodDominantEighthScoreCore_pos hApi)
  have hdominantLe : thetaCuspLikelihoodEighthDominantSingleMass A ≤ total := by
    rw [htotalSplit, hdominantEq]
    linarith
  have htotalPos : 0 < total := lt_of_lt_of_le hdominantPos hdominantLe
  have hfock := thetaCuspLikelihoodEighthFockOddWeight_lt_dominantSingleMass hx
  have hscaled : total < 256 / P * total := by
    nlinarith [mul_pos (sub_pos.mpr hfactor) htotalPos]
  have hsource := thetaCuspLikelihoodSourceOrdinaryJetEight_eq_spectralIntegral hx
  have hintegral := integral_thetaCuspLikelihoodEighthSourceScore_eq_tsum_atom A hB
  have hsourceEq : thetaCuspLikelihoodSourceOrdinaryJetEight x = 256 / P * total := by
    rw [hsource, hintegral]
  rw [hsourceEq]
  exact hfock.trans (lt_of_le_of_lt hdominantLe hscaled)

/-- Positive ordinary-source sandwich. -/
theorem thetaCuspLikelihoodEighthFockOrdinarySourceLanding
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodEighthFockOddWeight x ∧
      thetaCuspLikelihoodEighthFockOddWeight x <
        thetaCuspLikelihoodSourceOrdinaryJetEight x := by
  exact ⟨thetaCuspLikelihoodEighthFockOddWeight_pos hx,
    thetaCuspLikelihoodEighthFockOddWeight_lt_sourceOrdinaryJetEight hx⟩

end

end RHTower
