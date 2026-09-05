import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthEighthSpectralCoupling

/-!
# Scale-seven-halves dominant-pair sharpening

The global eighth-order Fock argument spends two thirds of dominant one-particle mass on the
coincident dominant pair.  Above source scale `A = 7/2`, recentering the exact degree-twenty
certificate proves the sharper absorption `(5/2) · pair < single`.  This raises retained Fock
mass from `544` to `1477` exponential units, retains `1/900` of the complete leading eighth
moment, and sharpens local sixth--eighth coupling from `1/69` to `1/26`.
-/

namespace RHTower

noncomputable section

set_option maxRecDepth 20000 in
/-- At scale `7/2`, the Taylor certificate absorbs five halves of dominant pair core. -/
theorem fiveHalves_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore_of_sevenHalves_le
    {A : ℝ} (hA : (7 / 2 : ℝ) ≤ A) :
    (5 / 2 : ℝ) * thetaCuspLikelihoodEighthDominantPairCore A <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        thetaCuspLikelihoodEighthDominantSingleCore A := by
  let B := A - 3 / 2
  have hB : 0 < B := by
    dsimp only [B]
    linarith
  change
    (5 / 2 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
        576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
        324 / B ^ 2 *
          thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
        (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
          18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A))
  let s := A - 7 / 2
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hmul : 0 < B ^ 10 *
      (thetaCuspLikelihoodEighthDominantTaylorTwenty A *
          (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
            18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)) -
        (5 / 2 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
          576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
          324 / B ^ 2 *
            thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A))) := by
    unfold thetaCuspLikelihoodEighthDominantTaylorTwenty
      thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform
      thetaCuspLikelihoodEighthSourceScoreRayTransform
      thetaCuspLikelihoodEighthSourceScore
      thetaCuspLikelihoodEighthSourceScoreDerivOne
      thetaCuspLikelihoodEighthSourceScoreDerivTwo
      thetaCuspLikelihoodEighthSourceScoreDerivThree
      thetaCuspLikelihoodEighthSourceScoreDerivFour
      thetaCuspLikelihoodEighthSourceScoreDerivFive
      thetaCuspLikelihoodEighthSourceScoreDerivSix
      thetaCuspLikelihoodEighthSourceScoreDerivSeven
      thetaCuspLikelihoodEighthSourceScoreDerivEight
    norm_num [Finset.sum_range_succ]
    field_simp [hB.ne']
    dsimp only [B]
    rw [show A = 7 / 2 + s by dsimp only [s]; ring]
    ring_nf
    positivity
  have hdiff : 0 <
      thetaCuspLikelihoodEighthDominantTaylorTwenty A *
          (16 * thetaCuspLikelihoodEighthSourceScore (3 * A) +
            18 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (3 * A)) -
        (5 / 2 : ℝ) * (256 * thetaCuspLikelihoodEighthSourceScore (6 * A) +
          576 / B * thetaCuspLikelihoodEighthSourceScoreRayTransform (A / B) (6 * A) +
          324 / B ^ 2 *
            thetaCuspLikelihoodEighthSourceScoreDoubleRayTransform (A / B) (6 * A)) :=
    pos_of_mul_pos_right hmul (pow_nonneg hB.le 10)
  linarith

/-- Restoring exponential weights preserves five-halves dominant-pair absorption. -/
theorem fiveHalves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass_of_sevenHalves_le
    {A : ℝ} (hA : (7 / 2 : ℝ) ≤ A) :
    (5 / 2 : ℝ) * thetaCuspLikelihoodEighthDominantPairMass A <
      thetaCuspLikelihoodEighthDominantSingleMass A := by
  have hAseam : (157 / 50 : ℝ) ≤ A := by linarith
  have hcore := fiveHalves_mul_thetaCuspLikelihoodEighthDominantPairCore_lt_taylor_mul_singleCore_of_sevenHalves_le hA
  have hsingle : 0 < thetaCuspLikelihoodEighthDominantSingleCore A := by
    simpa only [thetaCuspLikelihoodEighthDominantSingleCore] using
      thetaCuspLikelihoodDominantEighthScoreCore_pos hAseam
  have hexp : Real.exp (-(3 * A)) *
      thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤ 1 := by
    calc
      Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantTaylorTwenty A ≤
          Real.exp (-(3 * A)) * Real.exp (3 * A) := by
        gcongr
        exact thetaCuspLikelihoodEighthDominantTaylorTwenty_le_exp (by linarith)
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have habsorb : (5 / 2 : ℝ) *
      (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) <
      thetaCuspLikelihoodEighthDominantSingleCore A := by
    calc
      (5 / 2 : ℝ) *
          (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) =
          Real.exp (-(3 * A)) *
            ((5 / 2 : ℝ) * thetaCuspLikelihoodEighthDominantPairCore A) := by ring
      _ < Real.exp (-(3 * A)) *
          (thetaCuspLikelihoodEighthDominantTaylorTwenty A *
            thetaCuspLikelihoodEighthDominantSingleCore A) :=
        mul_lt_mul_of_pos_left hcore (Real.exp_pos _)
      _ = (Real.exp (-(3 * A)) *
          thetaCuspLikelihoodEighthDominantTaylorTwenty A) *
          thetaCuspLikelihoodEighthDominantSingleCore A := by ring
      _ ≤ 1 * thetaCuspLikelihoodEighthDominantSingleCore A := by gcongr
      _ = thetaCuspLikelihoodEighthDominantSingleCore A := one_mul _
  have hscale := mul_lt_mul_of_pos_left habsorb (Real.exp_pos (-(3 * A)))
  unfold thetaCuspLikelihoodEighthDominantPairMass
    thetaCuspLikelihoodEighthDominantSingleMass
  calc
    (5 / 2 : ℝ) *
        (Real.exp (-(6 * A)) * thetaCuspLikelihoodEighthDominantPairCore A) =
        Real.exp (-(3 * A)) * ((5 / 2 : ℝ) *
          (Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantPairCore A)) := by
      rw [show Real.exp (-(6 * A)) =
        Real.exp (-(3 * A)) * Real.exp (-(3 * A)) by
          rw [← Real.exp_add]
          congr 1
          ring]
      ring
    _ < Real.exp (-(3 * A)) * thetaCuspLikelihoodEighthDominantSingleCore A := hscale

/-- The scale-local Fock reserve retains 1477 dominant exponential units. -/
theorem oneThousandFourHundredSeventySeven_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight_of_sevenHalves_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (7 / 2 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    1477 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hApi : Real.pi ≤ A := by
    exact (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 7 / 2)).le.trans hA
  have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B, thetaCuspSingleAtomReflectionScale, thetaCuspLikelihoodCoordinate]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hdominant := fiveHalves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass_of_sevenHalves_le
    (A := A) (by simpa only [A] using hA)
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hAseam hBA
  have hnondom := thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp hApi hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_le hx
  have hsingle :=
    seventeenThousandFourHundredNinetySixFifths_mul_pow_eight_exp_lt_dominantSingleMass
      hApi hBA
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by positivity
  have hhigher' : thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (1300 / 3 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
    simpa only [A] using hhigher
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith [show
    (1477 : ℝ) + 376399 / 1999 + 1300 / 3 <
      (3 / 5 : ℝ) * (17496 / 5) by norm_num]

/-- Above scale `7/2`, one nine-hundredth of complete leading eighth mass survives. -/
theorem oneNineHundredth_mul_leadingEighthMoment_lt_fockWeight_of_sevenHalves_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (7 / 2 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1 / 900 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hApi : Real.pi ≤ A := by
    exact (Real.pi_lt_d4.trans (by norm_num : (3.1416 : ℝ) < 7 / 2)).le.trans hA
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B, thetaCuspSingleAtomReflectionScale, thetaCuspLikelihoodCoordinate]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_eq_spectralMoment A hB
  have hupper := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le hApi hBA
  rw [hmass] at hupper
  have hlower :=
    oneThousandFourHundredSeventySeven_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight_of_sevenHalves_le hx hA
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hupper
    (by norm_num : (0 : ℝ) ≤ 1 / 900)
  dsimp only [A, B] at hscaled hlower hscale ⊢
  nlinarith

/-- Literal log eighth jet retains `64/225` of normalized leading eighth moment locally. -/
theorem sixtyFourTwoHundredTwentyFifths_mul_leadingEighthMoment_lt_logJetEight_of_sevenHalves_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (7 / 2 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (64 / 225 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hlead := oneNineHundredth_mul_leadingEighthMoment_lt_fockWeight_of_sevenHalves_le hx hA
  have hfactor : 0 < 256 / P := div_pos (by norm_num) hP
  have hscaled := mul_lt_mul_of_pos_left hlead hfactor
  have hlanding := scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight hx
  calc
    (64 / 225 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 =
      (256 / P) * ((1 / 900 : ℝ) * A ^ 8 *
        thetaCuspHigherLikelihoodSpectralMoment B 8) := by
      dsimp only [A, B]
      unfold thetaCuspLikelihoodNormalizedMoment
      dsimp only [P]
      field_simp [hP.ne']
      ring
    _ < (256 / P) * thetaCuspLikelihoodEighthFockOddWeight x := by
      simpa only [A, B] using hscaled
    _ ≤ thetaCuspLikelihoodSourceLogPartitionJetEight x := by
      simpa only [B, P] using hlanding

/-- Scale-local sixth--eighth law: `J₈ > A² J₆ / 26` for `A ≥ 7/2`. -/
theorem oneTwentySixth_mul_scale_sq_logJetSix_lt_logJetEight_of_sevenHalves_le
    {x : ℝ} (hx : 0 ≤ x)
    (hA : (7 / 2 : ℝ) ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (1 / 26 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let m6 := thetaCuspLikelihoodNormalizedMoment B 6
  let m7 := thetaCuspLikelihoodNormalizedMoment B 7
  let m8 := thetaCuspLikelihoodNormalizedMoment B 8
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hordinary := thetaCuspLikelihoodSourceOrdinaryJetSix_le_leadingMoment hx
  have hlog :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  have hlog6Upper : thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1656 / 25 : ℝ) * A ^ 6 * m6 := by
    calc
      thetaCuspLikelihoodSourceLogPartitionJetSix x <
          (207 / 200 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := hlog
      _ ≤ (207 / 200 : ℝ) * (64 * A ^ 6 * m6) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [A, B, m6] using hordinary) (by norm_num)
      _ = (1656 / 25 : ℝ) * A ^ 6 * m6 := by ring
  have h67 : 3 * m6 ≤ m7 := by
    simpa only [B, m6, m7] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 6
  have h78 : 3 * m7 ≤ m8 := by
    simpa only [B, m7, m8] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 7
  have h68 : 9 * m6 ≤ m8 := by nlinarith
  have hlead8 :=
    sixtyFourTwoHundredTwentyFifths_mul_leadingEighthMoment_lt_logJetEight_of_sevenHalves_le hx hA
  have hmult : 0 < (1 / 26 : ℝ) * A ^ 2 := by positivity
  calc
    (1 / 26 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x =
      ((1 / 26 : ℝ) * A ^ 2) *
        thetaCuspLikelihoodSourceLogPartitionJetSix x := by rfl
    _ < ((1 / 26 : ℝ) * A ^ 2) *
        ((1656 / 25 : ℝ) * A ^ 6 * m6) :=
      mul_lt_mul_of_pos_left hlog6Upper hmult
    _ < (64 / 225 : ℝ) * A ^ 8 * (9 * m6) := by
      have hm4 := thetaCuspLikelihoodNormalizedMoment_four_pos hB
      have h45 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 4
      have h56 := three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 5
      have hm6 : 0 < m6 := by
        dsimp only [m6]
        nlinarith
      nlinarith [pow_pos (by positivity : 0 < A) 8]
    _ ≤ (64 / 225 : ℝ) * A ^ 8 * m8 := by
      exact mul_le_mul_of_nonneg_left h68 (by positivity)
    _ < thetaCuspLikelihoodSourceLogPartitionJetEight x := by
      simpa only [A, B, m8] using hlead8

end

end RHTower
