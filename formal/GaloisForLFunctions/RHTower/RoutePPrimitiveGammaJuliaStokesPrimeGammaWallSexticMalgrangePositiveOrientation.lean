import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.PrimeArchValuationSectorCones
import GaloisForLFunctions.RHTower.ThetaCuspCassiniCalibratedReciprocalMomentNoGo

/-!
# Positive orientation of the sixth prime/Gamma wall Malgrange jet

The all-order cold irregular-RH law identifies the sixth Malgrange correction with

`-60 * (normalizedPrimeArchMoment 5 - normalizedPrimeArchMoment 0 ^ (6 : ℕ) / 32)`.

The unconditional Schwarz-pair height gap puts every centered reciprocal-square Xi atom in the
disk of radius `231 / 9769`.  Four powers of this radius contract the absolute sixth moment to the
absolute second moment.  The centered sector law and the sharp fourth-trace source budget then
place that sixth moment below the forced first-jet scale.  Thus the sixth cold Stokes/Malgrange
target is strictly positive without an RH premise, zero selection, fitted wall clock, or numerical
computation.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Schwarz-pair height gap gives the corresponding sharp centered reciprocal-square radius. -/
theorem norm_xiZeroCopyReciprocalSquare_lt_twoHundredThirtyOne_over_nineThousandSevenHundredSixtyNine
    (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ < (231 / 9769 : ℝ) := by
  have hheight :=
    xiZeroCopy_nineThousandSevenHundredSixtyNine_div_twoHundredThirtyOne_lt_im_sq q
  have hspec : (9769 / 231 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    rw [norm_xiSpectralPoint, Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hspecpos : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow]
  have hinv :=
    (inv_lt_inv₀ hspecpos (by norm_num : (0 : ℝ) < 9769 / 231)).2 hspec
  norm_num at hinv ⊢
  exact hinv

/-- Four radius powers contract the absolute sixth centered moment to the absolute second moment. -/
theorem xiShiftAbsoluteMass_five_le_radius_pow_four_mul_one :
    xiShiftAbsoluteMass 5 ≤
      (231 / 9769 : ℝ) ^ (4 : ℕ) * xiShiftAbsoluteMass 1 := by
  rw [xiShiftAbsoluteMass, xiShiftAbsoluteMass, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro q
    have hnorm :=
      (norm_xiZeroCopyReciprocalSquare_lt_twoHundredThirtyOne_over_nineThousandSevenHundredSixtyNine
        q).le
    have hpow : ‖xiZeroCopyReciprocalSquare q‖ ^ (4 : ℕ) ≤ (231 / 9769 : ℝ) ^ (4 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 4
    change ‖xiZeroCopyReciprocalSquare q‖ ^ (6 : ℕ) ≤
      (231 / 9769 : ℝ) ^ (4 : ℕ) * ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ)
    calc
      ‖xiZeroCopyReciprocalSquare q‖ ^ (6 : ℕ) =
          ‖xiZeroCopyReciprocalSquare q‖ ^ (4 : ℕ) *
            ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) := by ring
      _ ≤ (231 / 9769 : ℝ) ^ (4 : ℕ) *
            ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  · exact summable_xiShiftAbsoluteMass 5
  · exact (summable_xiShiftAbsoluteMass 1).mul_left ((231 / 9769 : ℝ) ^ (4 : ℕ))

/-- Triangle inequality compares the actual sixth holomorphic trace with its absolute mass. -/
theorem normalizedPrimeArchMoment_five_le_xiShiftAbsoluteMass_five :
    normalizedPrimeArchMoment 5 ≤ xiShiftAbsoluteMass 5 := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow 5
  have hre : Summable (fun q : XiZeroCopy =>
      (xiZeroCopyReciprocalSquare q ^ (5 + 1)).re) :=
    Complex.reCLM.summable hpow
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow, Complex.re_tsum hpow,
    xiShiftAbsoluteMass]
  apply Summable.tsum_le_tsum
  · intro q
    rw [← norm_pow]
    exact Complex.re_le_norm (xiZeroCopyReciprocalSquare q ^ (5 + 1))
  · exact hre
  · exact summable_xiShiftAbsoluteMass 5

/-- The sixth cold residual lies strictly below its forced first-jet scale. -/
theorem normalizedPrimeArchMoment_five_sub_zero_pow_six_div_thirtyTwo_neg :
    normalizedPrimeArchMoment 5 - normalizedPrimeArchMoment 0 ^ (6 : ℕ) / 32 < 0 := by
  have hm5abs := normalizedPrimeArchMoment_five_le_xiShiftAbsoluteMass_five
  have hdecay := xiShiftAbsoluteMass_five_le_radius_pow_four_mul_one
  have hsector :=
    sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 1
  norm_num at hsector
  have hm1 := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  have habs1 : xiShiftAbsoluteMass 1 <
      (42 / 41 : ℝ) * (17 / 200000 : ℝ) := by
    nlinarith
  have hradiusPos : 0 < (231 / 9769 : ℝ) ^ (4 : ℕ) := by positivity
  have hmass5 : xiShiftAbsoluteMass 5 <
      (231 / 9769 : ℝ) ^ (4 : ℕ) * ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) :=
    hdecay.trans_lt (mul_lt_mul_of_pos_left habs1 hradiusPos)
  have hrat :
      (231 / 9769 : ℝ) ^ (4 : ℕ) * ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) <
        (1 / 25 : ℝ) ^ (6 : ℕ) / 32 := by
    norm_num
  have hm0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hm0pow : (1 / 25 : ℝ) ^ (6 : ℕ) < normalizedPrimeArchMoment 0 ^ (6 : ℕ) := by
    exact pow_lt_pow_left₀ hm0 (by norm_num) (by norm_num)
  have htarget : (1 / 25 : ℝ) ^ (6 : ℕ) / 32 <
      normalizedPrimeArchMoment 0 ^ (6 : ℕ) / 32 :=
    div_lt_div_of_pos_right hm0pow (by norm_num)
  linarith

/-- Exact positive scalar orientation of the canonical cold sixth Malgrange target. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallColdSixthMalgrangeTarget_pos :
    0 < -60 * (normalizedPrimeArchMoment 5 -
      normalizedPrimeArchMoment 0 ^ (6 : ℕ) / 32) := by
  nlinarith [normalizedPrimeArchMoment_five_sub_zero_pow_six_div_thirtyTwo_neg]

/-- Schwarz-pair radius contraction for every absolute centered-moment tail. -/
theorem xiShiftAbsoluteTail_le_schwarzPairRadius (s n : ℕ) :
    (∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n)) ≤
      (231 / 9769 : ℝ) ^ n * xiShiftAbsoluteMass s := by
  have hleft : Summable
      (fun q : XiZeroCopy =>
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n)) := by
    have h := (summable_xiZeroCopyReciprocalSquare_pow (s + n)).norm
    simpa only [norm_pow, show s + n + 1 = s + 1 + n by omega] using h
  rw [xiShiftAbsoluteMass, ← tsum_mul_left]
  exact hleft.tsum_le_tsum (fun q => by
    rw [pow_add]
    have hpow : ‖xiZeroCopyReciprocalSquare q‖ ^ n ≤ (231 / 9769 : ℝ) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_xiZeroCopyReciprocalSquare_lt_twoHundredThirtyOne_over_nineThousandSevenHundredSixtyNine
          q).le n
    exact (mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (norm_nonneg _) (s + 1))).trans_eq (mul_comm _ _))
    ((summable_xiShiftAbsoluteMass s).mul_left ((231 / 9769 : ℝ) ^ n))

/-- Every centered Xi moment obeys the sharp Schwarz-pair-radius absolute-tail envelope. -/
theorem abs_normalizedPrimeArchMoment_add_le_schwarzPairRadius_mul_xiShiftAbsoluteMass
    (s n : ℕ) :
    |normalizedPrimeArchMoment (s + n)| ≤
      (231 / 9769 : ℝ) ^ n * xiShiftAbsoluteMass s := by
  have hpow := summable_xiZeroCopyReciprocalSquare_pow (s + n)
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow]
  calc
    |(∑' q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q ^ (s + n + 1)).re| ≤
        ‖∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q ^ (s + n + 1)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q ^ (s + n + 1)‖ :=
      norm_tsum_le_tsum_norm hpow.norm
    _ = ∑' q : XiZeroCopy,
        ‖xiZeroCopyReciprocalSquare q‖ ^ (s + 1 + n) := by
      apply tsum_congr
      intro q
      rw [norm_pow]
      congr 1
      omega
    _ ≤ (231 / 9769 : ℝ) ^ n * xiShiftAbsoluteMass s :=
      xiShiftAbsoluteTail_le_schwarzPairRadius s n

/-- Every cold residual from the sixth through the fifteenth jet lies below its forced first-jet
scale. -/
theorem normalizedPrimeArchMoment_sub_firstJetScale_neg_of_five_le_of_le_fourteen
    (n : ℕ) (hnFive : 5 ≤ n) (hnFourteen : n ≤ 14) :
    normalizedPrimeArchMoment n -
      normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n < 0 := by
  have hsector :=
    sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 1
  norm_num at hsector
  have hm1 := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  have habs1 : xiShiftAbsoluteMass 1 <
      (42 / 41 : ℝ) * (17 / 200000 : ℝ) := by
    nlinarith
  have habsMomentRaw :=
    abs_normalizedPrimeArchMoment_add_le_schwarzPairRadius_mul_xiShiftAbsoluteMass
      1 (n - 1)
  have habsMoment : |normalizedPrimeArchMoment n| ≤
      (231 / 9769 : ℝ) ^ (n - 1) * xiShiftAbsoluteMass 1 := by
    simpa only [show 1 + (n - 1) = n by omega] using habsMomentRaw
  have hradiusPowPos : 0 < (231 / 9769 : ℝ) ^ (n - 1) := by positivity
  have hmUpper : normalizedPrimeArchMoment n <
      (231 / 9769 : ℝ) ^ (n - 1) *
        ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) :=
    (le_abs_self (normalizedPrimeArchMoment n)).trans habsMoment |>.trans_lt
      (mul_lt_mul_of_pos_left habs1 hradiusPowPos)
  have hrat :
      (231 / 9769 : ℝ) ^ (n - 1) *
          ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) <
        (1 / 25 : ℝ) ^ (n + 1) / (2 : ℝ) ^ n := by
    interval_cases n <;> norm_num
  have hm0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hm0pow : (1 / 25 : ℝ) ^ (n + 1) <
      normalizedPrimeArchMoment 0 ^ (n + 1) := by
    exact pow_lt_pow_left₀ hm0 (by norm_num) (Nat.succ_ne_zero n)
  have htarget : (1 / 25 : ℝ) ^ (n + 1) / (2 : ℝ) ^ n <
      normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n :=
    div_lt_div_of_pos_right hm0pow (pow_pos (by norm_num) n)
  linarith

/-- The cold Malgrange targets from orders six through fifteen have their exact alternating
orientation.  Multiplication by the expected parity sign makes every target strictly positive. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallColdMalgrangeTarget_signed_pos_of_five_le_of_le_fourteen
    (n : ℕ) (hnFive : 5 ≤ n) (hnFourteen : n ≤ 14) :
    0 < (-1 : ℝ) ^ (n + 1) *
      ((-1 : ℝ) ^ n * (n.factorial : ℝ) *
        (normalizedPrimeArchMoment n / 2 -
          (normalizedPrimeArchMoment 0 / 2) ^ (n + 1))) := by
  have hres :=
    normalizedPrimeArchMoment_sub_firstJetScale_neg_of_five_le_of_le_fourteen
      n hnFive hnFourteen
  have htwoPow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hscale :
      normalizedPrimeArchMoment n / 2 -
          (normalizedPrimeArchMoment 0 / 2) ^ (n + 1) =
        (normalizedPrimeArchMoment n -
          normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n) / 2 := by
    rw [div_pow, show (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 by rw [pow_succ]]
    field_simp [htwoPow]
  have hinner : normalizedPrimeArchMoment n / 2 -
      (normalizedPrimeArchMoment 0 / 2) ^ (n + 1) < 0 := by
    rw [hscale]
    nlinarith
  have hsign : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n = -1 := by
    rw [pow_succ]
    calc
      ((-1 : ℝ) ^ n * -1) * (-1 : ℝ) ^ n =
          -(((-1 : ℝ) ^ n) * (-1 : ℝ) ^ n) := by ring
      _ = -((-1 : ℝ) ^ (n + n)) := by rw [pow_add]
      _ = -((-1 : ℝ) ^ (2 * n)) := by rw [show n + n = 2 * n by omega]
      _ = -1 := by rw [pow_mul]; norm_num
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  calc
    (-1 : ℝ) ^ (n + 1) *
        ((-1 : ℝ) ^ n * (n.factorial : ℝ) *
          (normalizedPrimeArchMoment n / 2 -
            (normalizedPrimeArchMoment 0 / 2) ^ (n + 1))) =
      ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n) *
        (n.factorial : ℝ) *
          (normalizedPrimeArchMoment n / 2 -
            (normalizedPrimeArchMoment 0 / 2) ^ (n + 1)) := by ring
    _ = -1 * (n.factorial : ℝ) *
          (normalizedPrimeArchMoment n / 2 -
            (normalizedPrimeArchMoment 0 / 2) ^ (n + 1)) := by rw [hsign]
    _ > 0 := by nlinarith

end

end RHTower
