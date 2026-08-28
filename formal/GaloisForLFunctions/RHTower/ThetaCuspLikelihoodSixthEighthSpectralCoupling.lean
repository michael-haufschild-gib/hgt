import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthSpectralDecomposition
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthLogPositivity

/-!
# Shared-spectrum coupling of sixth and eighth theta likelihood jets

The sharp support edge of the fixed higher-theta spectral measure propagates sixth moments into
eighth moments.  Exact Fock absorption supplies a quantitative fraction of the leading eighth
moment inside the literal logarithmic eighth jet.  Together these facts give a global, source-
faithful comparison between the literal sixth and eighth logarithmic jets.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The ordinary sixth score is bounded above by its leading spectral monomial. -/
theorem thetaCuspLikelihoodSourceOrdinaryJetSix_le_leadingMoment
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceOrdinaryJetSix x ≤
      64 * thetaCuspSingleAtomReflectionScale 1 x ^ 6 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 6 := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hA : (47 / 15 : ℝ) < A := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    have hmul : Real.pi ≤ Real.pi * Real.exp (2 * x) :=
      le_mul_of_one_le_right Real.pi_pos.le he
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    nlinarith [Real.pi_gt_d2]
  have hscore := integrable_thetaLikelihoodSixthScore_mul_exp_neg_higherSpectral A hB
  have hlead0 :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 6 hB).const_mul
      (A ^ 6)
  have hlead : Integrable (fun t : ℝ =>
      (A * t) ^ 6 * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
    convert hlead0 using 1
    funext t
    ring
  have hpoint : ∀ᵐ t ∂thetaCuspHigherLikelihoodSpectralMeasure,
      thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t)) ≤
        (A * t) ^ 6 * Real.exp (-(B * t)) := by
    filter_upwards [ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
    have hAt : (47 / 5 : ℝ) < A * t := by
      nlinarith [mul_lt_mul_of_pos_right hA (show 0 < t by linarith)]
    exact mul_le_mul_of_nonneg_right (thetaLikelihoodSixthScore_le_pow_six hAt)
      (Real.exp_pos _).le
  have hint := integral_mono_ae hscore hlead hpoint
  have hleadEq :
      (∫ t : ℝ, (A * t) ^ 6 * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) =
        A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 := by
    rw [show (fun t : ℝ => (A * t) ^ 6 * Real.exp (-(B * t))) =
        fun t => A ^ 6 * (t ^ 6 * Real.exp (-(B * t))) by
      funext t
      ring]
    rw [integral_const_mul,
      thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hleadEq] at hint
  rw [thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral hx]
  change 64 / P * _ ≤ 64 * A ^ 6 *
    (thetaCuspHigherLikelihoodSpectralMoment B 6 / P)
  have hcoeff : 0 ≤ 64 / P := div_nonneg (by norm_num) hP.le
  calc
    64 / P * _ ≤ 64 / P * (A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6) :=
      mul_le_mul_of_nonneg_left hint hcoeff
    _ = 64 * A ^ 6 * (thetaCuspHigherLikelihoodSpectralMoment B 6 / P) := by
      field_simp [hP.ne']

/-- After all pair and higher-even Fock losses, at least `1/2600` of the complete leading
eighth spectral monomial remains. -/
theorem oneTwentySixHundredth_mul_leadingEighthMoment_lt_fockWeight
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2600 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hBA : B = A - 3 / 2 := by
    dsimp [A, B, thetaCuspLikelihoodCoordinate, thetaCuspSingleAtomReflectionScale]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_eq_spectralMoment A hB
  have hupper := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le hA hBA
  rw [hmass] at hupper
  have hlower :=
    fiveHundred_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight hx
  have hscaled := mul_le_mul_of_nonneg_left hupper
    (by norm_num : (0 : ℝ) ≤ 1 / 2600)
  dsimp only [A, B] at hscaled hlower ⊢
  nlinarith

/-- The literal logarithmic eighth jet retains `32/325` of its normalized leading spectral
monomial. -/
theorem thirtyTwoThreeHundredTwentyFifths_mul_leadingEighthMoment_lt_logJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (32 / 325 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hlead := oneTwentySixHundredth_mul_leadingEighthMoment_lt_fockWeight hx
  have hfactor : 0 < 256 / P := div_pos (by norm_num) hP
  have hscaled := mul_lt_mul_of_pos_left hlead hfactor
  have hlanding := scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight hx
  calc
    (32 / 325 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 =
      (256 / P) * ((1 / 2600 : ℝ) * A ^ 8 *
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

/-- **Sixth--eighth spectral coupling.** The literal logarithmic eighth likelihood jet strictly
dominates `9/676` times the squared source scale times the literal sixth logarithmic jet. -/
theorem nineSixHundredSeventySixths_mul_scale_sq_logJetSix_lt_logJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (9 / 676 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let m6 := thetaCuspLikelihoodNormalizedMoment B 6
  let m7 := thetaCuspLikelihoodNormalizedMoment B 7
  let m8 := thetaCuspLikelihoodNormalizedMoment B 8
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hordinary := thetaCuspLikelihoodSourceOrdinaryJetSix_le_leadingMoment hx
  have hlog6 :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twentySixTwentyFifths_ordinary hx
  have hlog6Upper : thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1664 / 25 : ℝ) * A ^ 6 * m6 := by
    calc
      thetaCuspLikelihoodSourceLogPartitionJetSix x <
          (26 / 25 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := hlog6
      _ ≤ (26 / 25 : ℝ) * (64 * A ^ 6 * m6) := by
        have hcoeff : (0 : ℝ) ≤ 26 / 25 := by norm_num
        exact mul_le_mul_of_nonneg_left
          (by simpa only [A, B, m6] using hordinary) hcoeff
      _ = (1664 / 25 : ℝ) * A ^ 6 * m6 := by ring
  have h67 : 3 * m6 ≤ m7 := by
    simpa only [B, m6, m7] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 6
  have h78 : 3 * m7 ≤ m8 := by
    simpa only [B, m7, m8] using
      three_mul_thetaCuspLikelihoodNormalizedMoment_le_succ hB 7
  have h68 : 9 * m6 ≤ m8 := by nlinarith
  have hlead8 :=
    thirtyTwoThreeHundredTwentyFifths_mul_leadingEighthMoment_lt_logJetEight hx
  have hmult : 0 < (9 / 676 : ℝ) * A ^ 2 := by positivity
  calc
    (9 / 676 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x =
      ((9 / 676 : ℝ) * A ^ 2) *
        thetaCuspLikelihoodSourceLogPartitionJetSix x := by rfl
    _ < ((9 / 676 : ℝ) * A ^ 2) *
        ((1664 / 25 : ℝ) * A ^ 6 * m6) :=
      mul_lt_mul_of_pos_left hlog6Upper hmult
    _ = (32 / 325 : ℝ) * A ^ 8 * (9 * m6) := by ring
    _ ≤ (32 / 325 : ℝ) * A ^ 8 * m8 := by
      exact mul_le_mul_of_nonneg_left h68 (by positivity)
    _ < thetaCuspLikelihoodSourceLogPartitionJetEight x := by
      simpa only [A, B, m8] using hlead8

/-! ### Sharpened retained-Fock coupling -/

/-- The exact existing Fock budgets retain 544, rather than merely 500, dominant exponential
units. -/
theorem fiveHundredFortyFour_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight
    {x : ℝ} (hx : 0 ≤ x) :
    544 * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        Real.exp (-(3 * thetaCuspSingleAtomReflectionScale 1 x)) <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
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
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hdominant :=
    three_halves_mul_thetaCuspLikelihoodEighthDominantPairMass_lt_singleMass hApi
  have htwo := thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hApi hBA
  have hnondom := thetaCuspLikelihoodNonDominantPairEighthTail_le_sharp hA hBA
  have hhigher := thetaCuspLikelihoodEighthHigherEvenFockLoss_le hx
  have hsingle :=
    seventeenThousandFourHundredNinetySixFifths_mul_pow_eight_exp_lt_dominantSingleMass
      hA hBA
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := Real.pi_pos.trans_le hA
    positivity
  have hhigher' : thetaCuspLikelihoodEighthHigherEvenFockLoss x ≤
      (1300 / 3 : ℝ) * A ^ 8 * Real.exp (-(3 * A)) := by
    simpa only [A] using hhigher
  unfold thetaCuspLikelihoodEighthFockOddWeight
  dsimp only [A, B]
  unfold thetaCuspLikelihoodEighthPairSectorMass
  rw [htwo]
  nlinarith [show
    (544 : ℝ) + 376399 / 1999 + 1300 / 3 < 5832 / 5 by norm_num]

/-- The sharpened Fock budget retains `1/2400` of the complete leading eighth monomial. -/
theorem oneOverTwoThousandFourHundred_mul_leadingEighthMoment_lt_fockWeight
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 2400 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodEighthFockOddWeight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : Real.pi ≤ A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hBA : B = A - 3 / 2 := by
    dsimp [A, B, thetaCuspLikelihoodCoordinate, thetaCuspSingleAtomReflectionScale]
    norm_num
    rw [show Real.exp (2 * x) = Real.exp x ^ 2 by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hmass := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_eq_spectralMoment A hB
  have hupper := tsum_thetaCuspLikelihoodAtomEighthMonomialMass_le hA hBA
  rw [hmass] at hupper
  have hlower :=
    fiveHundredFortyFour_mul_pow_eight_exp_lt_thetaCuspLikelihoodEighthFockOddWeight hx
  have hscale : 0 < A ^ 8 * Real.exp (-(3 * A)) := by
    have hA0 : 0 < A := Real.pi_pos.trans_le hA
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hupper
    (by norm_num : (0 : ℝ) ≤ 1 / 2400)
  dsimp only [A, B] at hscaled hlower hscale ⊢
  nlinarith

/-- The literal logarithmic eighth jet retains `8/75` of its normalized leading spectral
monomial. -/
theorem eightSeventyFifths_mul_leadingEighthMoment_lt_logJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (8 / 75 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hP : 0 < P := by simpa only [P] using thetaCuspLikelihoodPartition_pos hB
  have hlead := oneOverTwoThousandFourHundred_mul_leadingEighthMoment_lt_fockWeight hx
  have hfactor : 0 < 256 / P := div_pos (by norm_num) hP
  have hscaled := mul_lt_mul_of_pos_left hlead hfactor
  have hlanding := scaled_thetaCuspLikelihoodEighthFockOddWeight_le_sourceLogPartitionJetEight hx
  calc
    (8 / 75 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 8 *
        thetaCuspLikelihoodNormalizedMoment (thetaCuspLikelihoodCoordinate x) 8 =
      (256 / P) * ((1 / 2400 : ℝ) * A ^ 8 *
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

/-- **Sharp sixth--eighth spectral coupling.** The literal logarithmic eighth jet strictly
dominates `1/69` times squared source scale times the literal logarithmic sixth jet. -/
theorem oneSixtyNinth_mul_scale_sq_logJetSix_lt_logJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (1 / 69 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let m6 := thetaCuspLikelihoodNormalizedMoment B 6
  let m7 := thetaCuspLikelihoodNormalizedMoment B 7
  let m8 := thetaCuspLikelihoodNormalizedMoment B 8
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have hA : 0 < A := by
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hordinary := thetaCuspLikelihoodSourceOrdinaryJetSix_le_leadingMoment hx
  have hlog6 :=
    thetaCuspLikelihoodSourceLogPartitionJetSix_lt_twoHundredSevenTwoHundredths_ordinary hx
  have hlog6Upper : thetaCuspLikelihoodSourceLogPartitionJetSix x <
      (1656 / 25 : ℝ) * A ^ 6 * m6 := by
    calc
      thetaCuspLikelihoodSourceLogPartitionJetSix x <
          (207 / 200 : ℝ) * thetaCuspLikelihoodSourceOrdinaryJetSix x := hlog6
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
  have hlead8 := eightSeventyFifths_mul_leadingEighthMoment_lt_logJetEight hx
  have hmult : 0 < (1 / 69 : ℝ) * A ^ 2 := by positivity
  calc
    (1 / 69 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x =
      ((1 / 69 : ℝ) * A ^ 2) *
        thetaCuspLikelihoodSourceLogPartitionJetSix x := by rfl
    _ < ((1 / 69 : ℝ) * A ^ 2) *
        ((1656 / 25 : ℝ) * A ^ 6 * m6) :=
      mul_lt_mul_of_pos_left hlog6Upper hmult
    _ = (8 / 75 : ℝ) * A ^ 8 * (9 * m6) := by ring
    _ ≤ (8 / 75 : ℝ) * A ^ 8 * m8 := by
      exact mul_le_mul_of_nonneg_left h68 (by positivity)
    _ < thetaCuspLikelihoodSourceLogPartitionJetEight x := by
      simpa only [A, B, m8] using hlead8

/-- Compatibility form of the first sharpened coupling constant. -/
theorem threeTwoHundredEighths_mul_scale_sq_logJetSix_lt_logJetEight
    {x : ℝ} (hx : 0 ≤ x) :
    (3 / 208 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
        thetaCuspLikelihoodSourceLogPartitionJetSix x <
      thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  have hsharp := oneSixtyNinth_mul_scale_sq_logJetSix_lt_logJetEight hx
  have hA : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have h6 := thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx
  have hscaled :
      (3 / 208 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
          thetaCuspLikelihoodSourceLogPartitionJetSix x <
        (1 / 69 : ℝ) * thetaCuspSingleAtomReflectionScale 1 x ^ 2 *
          thetaCuspLikelihoodSourceLogPartitionJetSix x := by
    have hcoeff : (3 / 208 : ℝ) < 1 / 69 := by norm_num
    exact mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hA)) h6
  exact hscaled.trans hsharp

end

end RHTower
