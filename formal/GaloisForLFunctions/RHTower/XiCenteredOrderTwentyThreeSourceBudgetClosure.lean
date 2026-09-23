import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyTwoSourceBudgetClosure

/-!
# Centered order-23 source-budget closure

The corrected Euler--Mascheroni upper sequence lowers completed endpoint
curvature below `231 / 5000`.  Combined with the existing sixty-fourth-mesh
theta floor, this contracts the complete fourth reciprocal trace below
`17 / 200000`.

An optimized sector certificate with `N = 215`, `t = 341 / 5000` confines
any failure of reciprocal-square power 23 to a compact annulus.  Every atom
there spends more than one quarter of the trace budget, so FE--Schwarz
symmetry empties the annulus and proves positivity of source moment 22.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Corrected Euler control sharpens the completed endpoint curvature. -/
theorem xiEndpointCompletedCurvature_lt_twoHundredThirtyOne_over_fiveThousand :
    xiEndpointCompletedCurvature < 231 / 5000 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  nlinarith
    [eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion,
      twoHundredFiftyThreeThousandOneHundredTwo_over_oneHundredThousand_lt_log_four_mul_pi]

/-- Coupled endpoint-resolvent control places the zeroth source below `0.04623`. -/
theorem normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredTwentyThree_over_oneHundredThousand :
    normalizedPrimeArchMoment 0 < 4623 / 100000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM1 : M < 1 := by
    simpa only [M] using normalizedPrimeArchMoment_zero_lt_one
  have hmu :=
    twoThousandNineHundredFiftyOne_div_fiveHundredThousand_lt_thetaCuspNormalizedEvenMoment_two
  have hsource : normalizedPrimeArchMoment 1 <
      M ^ (2 : ℕ) / 2 - (2951 / 500000 : ℝ) / 6 := by
    rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
      ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [M]
    nlinarith
  have hthermal : xiThermalSecondMoment <
      (84 / 83 : ℝ) * (M ^ (2 : ℕ) / 2 - (2951 / 500000 : ℝ) / 6) :=
    xiThermalSecondMoment_le_eightyFour_over_eightyThree_source.trans_lt
      (mul_lt_mul_of_pos_left hsource (by norm_num))
  have hgap :=
    normalizedPrimeArchMoment_zero_sub_thermalEndpointResolvent_le_quarter_secondMoment
  have hres := xiThermalEndpointResolventValue_le_endpointCompletedCurvature
  have hC := xiEndpointCompletedCurvature_lt_twoHundredThirtyOne_over_fiveThousand
  have hmaster :
      M < 231 / 5000 +
        (21 / 83 : ℝ) * (M ^ (2 : ℕ) / 2 - (2951 / 500000 : ℝ) / 6) := by
    dsimp only [M] at hgap ⊢
    nlinarith
  by_contra hnot
  have hMlower : (4623 / 100000 : ℝ) ≤ M := le_of_not_gt hnot
  have hfactor : 0 < 1 - (21 / 166 : ℝ) * (M + 4623 / 100000) := by
    nlinarith
  have hmonotone :
      (4623 / 100000 : ℝ) - (21 / 166 : ℝ) * (4623 / 100000) ^ (2 : ℕ) ≤
        M - (21 / 166 : ℝ) * M ^ (2 : ℕ) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hMlower) hfactor.le
    nlinarith
  have hupper :
      M - (21 / 166 : ℝ) * M ^ (2 : ℕ) <
        231 / 5000 - (21 / 498 : ℝ) * (2951 / 500000) := by
    nlinarith [hmaster]
  have hrat :
      231 / 5000 - (21 / 498 : ℝ) * (2951 / 500000) <
        (4623 / 100000 : ℝ) - (21 / 166 : ℝ) * (4623 / 100000) ^ (2 : ℕ) := by
    norm_num
  linarith

/-- Sharpened complete fourth reciprocal-trace budget. -/
theorem normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand :
    normalizedPrimeArchMoment 1 < 17 / 200000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM0 : 0 < M := by
    simpa only [M] using normalizedPrimeArchMoment_zero_pos
  have hM :=
    normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredTwentyThree_over_oneHundredThousand
  have hMsq : M ^ (2 : ℕ) < (4623 / 100000 : ℝ) ^ (2 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr (by simpa only [M] using hM))
      (add_pos (by norm_num : (0 : ℝ) < 4623 / 100000) hM0)
    nlinarith
  have hmu :=
    twoThousandNineHundredFiftyOne_div_fiveHundredThousand_lt_thetaCuspNormalizedEvenMoment_two
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  simpa only [M] using (by nlinarith :
    M ^ (2 : ℕ) / 2 - thetaCuspNormalizedEvenMoment 2 / 6 < 17 / 200000)

theorem orderTwentyThreeReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 215 * B ^ (2 : ℕ) < A ^ (2 : ℕ)) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (23 : ℕ)).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt
    (t := 341 / 5000) hA (by norm_num) (by norm_num) hsector
    (by norm_num; nlinarith [Real.pi_gt_d20])

theorem xiCenteredOrderTwentyThreeSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ≤ (2365 / 13792 : ℝ)) :
    215 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hv : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ (2 : ℕ) :=
    le_of_not_gt fun hvlt => hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hvlt)
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 215)
      (u₀ := 2365 / 13792) (v₀ := 2365 / 16) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl hinner hv (by norm_num) (by norm_num)

theorem xiCenteredOrderTwentyThreeSectorRatio_of_fourHundredThirtyOneHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 431 / 2 ≤ (q.1 : ℂ).im ^ (2 : ℕ)) :
    215 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) <
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 215)
      (u₀ := 1 / 4) (v₀ := 431 / 2) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh
      (by norm_num) (by norm_num)

def XiCenteredOrderTwentyThreeResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 13792 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ) ∧
          (q.1 : ℂ).im ^ (2 : ℕ) < 431 / 2

theorem xiCenteredOrderTwentyThreeSectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
        215 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ)) :
    XiCenteredOrderTwentyThreeResidualAnnulus q := by
  refine ⟨hoff, ?_, xi_divisor_support_centered_re_sq_lt_quarter q.1, ?_, ?_⟩
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyThreeSectorRatio_of_offLine_inner q hoff (not_lt.mp h))
      (not_lt.mpr hfail)
  · by_contra h
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (not_le.mp h))
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyThreeSectorRatio_of_fourHundredThirtyOneHalves_le_im_sq q
        (not_lt.mp h))
      (not_lt.mpr hfail)

theorem xiZeroCopyReciprocalSquare_pow_twentyThree_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyThreeResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ (23 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderTwentyThreeReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderTwentyThreeSectorFailure_mem_residualAnnulus q hoff hfail)
    hnot

def XiCenteredOrderTwentyThreeResidualAnnulusEmpty : Prop :=
  ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyThreeResidualAnnulus q

/-- Every fourth-trace atom in the order-23 residual annulus exceeds one quarter
of the complete trace cap. -/
theorem seventeen_over_eightHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyThree
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 431 / 2) :
    (17 / 800000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let w : ℝ := u + v
  let W : ℝ := 863 / 4
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 431 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 2365 / 16 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ (2 : ℕ) < W ^ (2 : ℕ) :=
    (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsqLower : (2365 / 16 : ℝ) ^ (2 : ℕ) < w ^ (2 : ℕ) :=
    (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
  have hsecond : 0 < 17 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 800000 := by
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      800000 * W ^ (2 : ℕ) - 17 * W ^ (4 : ℕ) <
        800000 * w ^ (2 : ℕ) - 17 * w ^ (4 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (800000 * w ^ (2 : ℕ) - 17 * w ^ (4 : ℕ)) -
            (800000 * W ^ (2 : ℕ) - 17 * W ^ (4 : ℕ)) =
          (W ^ (2 : ℕ) - w ^ (2 : ℕ)) * (17 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 800000) := by
      ring
    nlinarith
  have huv : u * v < 431 / 8 := by
    calc
      u * v < (1 / 4 : ℝ) * v := mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (431 / 2) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 431 / 8 := by ring
  have hendpoint :
      6400000 * (431 / 8 : ℝ) <
        800000 * W ^ (2 : ℕ) - 17 * W ^ (4 : ℕ) := by
    norm_num [W]
  have huvScaled : 6400000 * (u * v) < 6400000 * (431 / 8 : ℝ) :=
    mul_lt_mul_of_pos_left huv (by norm_num)
  have hchain :
      6400000 * (u * v) < 800000 * w ^ (2 : ℕ) - 17 * w ^ (4 : ℕ) :=
    huvScaled.trans (hendpoint.trans hshape)
  have hG :
      0 < 800000 * (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) - 17 * w ^ (4 : ℕ) := by
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
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 800000) (pow_pos hw0 4)]
  nlinarith

theorem seventeen_over_twoHundredThousand_lt_source_of_centeredOrderTwentyThreeResidualAnnulus
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyThreeResidualAnnulus q) :
    (17 / 200000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hq.1
  have hatom :=
    seventeen_over_eightHundredThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyThree
      q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  nlinarith

theorem xiCenteredOrderTwentyThreeResidualAnnulusEmpty :
    XiCenteredOrderTwentyThreeResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  have hlower :=
    seventeen_over_twoHundredThousand_lt_source_of_centeredOrderTwentyThreeResidualAnnulus q hq
  have hupper := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  linarith

theorem xiZeroCopyReciprocalSquare_pow_twentyThree_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ (23 : ℕ)).re :=
  xiZeroCopyReciprocalSquare_pow_twentyThree_re_pos_of_not_mem_residualAnnulus q
    (fun hq => xiCenteredOrderTwentyThreeResidualAnnulusEmpty ⟨q, hq⟩)

/-- Unconditional positivity of the centered source moment of order 22. -/
theorem normalizedPrimeArchMoment_twentyTwo_pos :
    0 < normalizedPrimeArchMoment 22 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 22
  simpa using xiZeroCopyReciprocalSquare_pow_twentyThree_re_pos

end

end RHTower
