import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentSixtyFourthFloor
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyOneSourceBudgetClosure

/-!
# Centered order-22 source-budget closure

The sharpened sixty-fourth-mesh theta certificate lowers the complete fourth
reciprocal trace below `9 / 100000`.  Every atom in the only sector-failure
annulus for reciprocal-square power 22 contributes more than one quarter of
that budget.  FE--Schwarz symmetry therefore empties the annulus and proves
positivity of `normalizedPrimeArchMoment 21` unconditionally.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem twoThousandNineHundredFiftyOne_div_fiveHundredThousand_lt_thetaCuspNormalizedEvenMoment_two :
    (2951 / 500000 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  have hraw2 : (2951 / 1000000 : ℝ) < thetaCuspRawEvenMoment 2 :=
    twoThousandNineHundredFiftyOne_div_oneMillion_lt_thetaCuspAtomRawEvenMoment_two_one.trans_le
      (thetaCuspAtomRawEvenMoment_one_le_raw 2)
  have hraw0pos : 0 < thetaCuspRawEvenMoment 0 :=
    thetaCuspRawEvenMoment_zero_pos
  have hraw1nonneg : 0 ≤ thetaCuspRawEvenMoment 1 :=
    thetaCuspRawEvenMoment_nonneg 1
  have hraw0le : thetaCuspRawEvenMoment 0 ≤ 1 / 2 := by
    nlinarith [thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget]
  rw [thetaCuspNormalizedEvenMoment, lt_div_iff₀ hraw0pos]
  nlinarith

theorem normalizedPrimeArchMoment_one_lt_nine_over_oneHundredThousand :
    normalizedPrimeArchMoment 1 < 9 / 100000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM :=
    normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredThirtyThree_over_oneHundredThousand
  have hM0 : 0 < M := by
    simpa only [M] using normalizedPrimeArchMoment_zero_pos
  have hMsq : M ^ (2 : ℕ) < (4633 / 100000 : ℝ) ^ (2 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr (by simpa only [M] using hM))
      (add_pos (by norm_num : (0 : ℝ) < 4633 / 100000) hM0)
    nlinarith
  have hmu :=
    twoThousandNineHundredFiftyOne_div_fiveHundredThousand_lt_thetaCuspNormalizedEvenMoment_two
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  simpa only [M] using (by nlinarith :
    M ^ (2 : ℕ) / 2 - thetaCuspNormalizedEvenMoment 2 / 6 < 9 / 100000)

theorem orderTwentyTwoReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 205 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (22 : ℕ)).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt
    (t := 7 / 100) hA (by norm_num) (by norm_num) hsector
    (by norm_num; nlinarith [Real.pi_gt_d20])

theorem xiCenteredOrderTwentyTwoSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (2365 / 13152 : ℝ)) :
    205 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hv : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ (2 : ℕ) :=
    le_of_not_gt fun hvlt => hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hvlt)
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 205)
      (u₀ := 2365 / 13152) (v₀ := 2365 / 16) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl hinner hv (by norm_num) (by norm_num)

theorem xiCenteredOrderTwentyTwoSectorRatio_of_fourHundredElevenHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 411 / 2 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    205 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 205)
      (u₀ := 1 / 4) (v₀ := 411 / 2) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh
      (by norm_num) (by norm_num)

def XiCenteredOrderTwentyTwoResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 13152 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) ∧
          (q.1 : ℂ).im ^ (2 : ℕ) < 411 / 2

theorem xiCenteredOrderTwentyTwoSectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        205 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    XiCenteredOrderTwentyTwoResidualAnnulus q := by
  refine ⟨hoff, ?_, xi_divisor_support_centered_re_sq_lt_quarter q.1, ?_, ?_⟩
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyTwoSectorRatio_of_offLine_inner q hoff (not_lt.mp h))
      (not_lt.mpr hfail)
  · by_contra h
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (not_le.mp h))
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyTwoSectorRatio_of_fourHundredElevenHalves_le_im_sq q
        (not_lt.mp h))
      (not_lt.mpr hfail)

theorem xiZeroCopyReciprocalSquare_pow_twentyTwo_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyTwoResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ (22 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderTwentyTwoReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderTwentyTwoSectorFailure_mem_residualAnnulus q hoff hfail)
    hnot

def XiCenteredOrderTwentyTwoResidualAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyTwoResidualAnnulus q

theorem nine_over_fourHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyTwo
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 411 / 2) :
    (9 / 400000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let w : ℝ := u + v
  let W : ℝ := 823 / 4
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 411 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 2365 / 16 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ (2 : ℕ) < W ^ (2 : ℕ) :=
    (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsqLower : (2365 / 16 : ℝ) ^ (2 : ℕ) < w ^ (2 : ℕ) :=
    (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
  have hsecond : 0 < 9 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 400000 := by
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      400000 * W ^ (2 : ℕ) - 9 * W ^ (4 : ℕ) <
        400000 * w ^ (2 : ℕ) - 9 * w ^ (4 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (400000 * w ^ (2 : ℕ) - 9 * w ^ (4 : ℕ)) -
            (400000 * W ^ (2 : ℕ) - 9 * W ^ (4 : ℕ)) =
          (W ^ (2 : ℕ) - w ^ (2 : ℕ)) * (9 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 400000) := by
      ring
    nlinarith
  have huv : u * v < 411 / 8 := by
    calc
      u * v < (1 / 4 : ℝ) * v := mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (411 / 2) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 411 / 8 := by ring
  have hendpoint :
      3200000 * (411 / 8 : ℝ) <
        400000 * W ^ (2 : ℕ) - 9 * W ^ (4 : ℕ) := by
    norm_num [W]
  have huvScaled : 3200000 * (u * v) < 3200000 * (411 / 8 : ℝ) :=
    mul_lt_mul_of_pos_left huv (by norm_num)
  have hchain :
      3200000 * (u * v) < 400000 * w ^ (2 : ℕ) - 9 * w ^ (4 : ℕ) :=
    huvScaled.trans (hendpoint.trans hshape)
  have hG :
      0 < 400000 * (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) - 9 * w ^ (4 : ℕ) := by
    have hN : v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ) = w ^ (2 : ℕ) - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith [hchain]
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re =
        (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) / w ^ (4 : ℕ) := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 400000) (pow_pos hw0 4)]
  nlinarith

theorem nine_over_oneHundredThousand_lt_source_of_centeredOrderTwentyTwoResidualAnnulus
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyTwoResidualAnnulus q) :
    (9 / 100000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hq.1
  have hatom := nine_over_fourHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyTwo
    q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  nlinarith

theorem xiCenteredOrderTwentyTwoResidualAnnulusEmpty :
    XiCenteredOrderTwentyTwoResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  have hlower :=
    nine_over_oneHundredThousand_lt_source_of_centeredOrderTwentyTwoResidualAnnulus q hq
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_oneHundredThousand
  linarith

theorem xiZeroCopyReciprocalSquare_pow_twentyTwo_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (22 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_twentyTwo_re_pos_of_not_mem_residualAnnulus q
    (fun hq => xiCenteredOrderTwentyTwoResidualAnnulusEmpty ⟨q, hq⟩)

theorem normalizedPrimeArchMoment_twentyOne_pos :
    0 < normalizedPrimeArchMoment 21 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 21
  simpa using xiZeroCopyReciprocalSquare_pow_twentyTwo_re_pos

end

end RHTower
