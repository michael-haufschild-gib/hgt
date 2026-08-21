import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyOneSixthTraceFloor

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every fourth reciprocal-trace atom throughout the order-twenty-one residual annulus
exceeds `3 / 100000`. -/
theorem three_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 361 / 2) :
    (3 / 100000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 723 / 4
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 361 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 2365 / 16 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ 2 < W ^ 2 :=
    (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsqLower : (2365 / 16 : ℝ) ^ 2 < w ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
  have hsecond : 0 < 3 * (W ^ 2 + w ^ 2) - 100000 := by
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      100000 * W ^ 2 - 3 * W ^ 4 <
        100000 * w ^ 2 - 3 * w ^ 4 := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (100000 * w ^ 2 - 3 * w ^ 4) -
            (100000 * W ^ 2 - 3 * W ^ 4) =
          (W ^ 2 - w ^ 2) * (3 * (W ^ 2 + w ^ 2) - 100000) := by
      ring
    nlinarith
  have huv : u * v < 361 / 8 := by
    calc
      u * v < (1 / 4 : ℝ) * v := mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (361 / 2) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 361 / 8 := by ring
  have hendpoint :
      800000 * (361 / 8 : ℝ) <
        100000 * W ^ 2 - 3 * W ^ 4 := by
    norm_num [W]
  have huvScaled : 800000 * (u * v) < 800000 * (361 / 8 : ℝ) :=
    mul_lt_mul_of_pos_left huv (by norm_num)
  have hchain :
      800000 * (u * v) < 100000 * w ^ 2 - 3 * w ^ 4 :=
    huvScaled.trans (hendpoint.trans hshape)
  have hG :
      0 < 100000 * (v ^ 2 - 6 * u * v + u ^ 2) - 3 * w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith [hchain]
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ 2).re =
        (v ^ 2 - 6 * u * v + u ^ 2) / w ^ 4 := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 100000) (pow_pos hw0 4)]
  nlinarith

/-- One residual-annulus zero forces more than `3 / 25000` of complete fourth trace. -/
theorem three_over_twentyFiveThousand_lt_source_of_centeredOrderTwentyOneResidualAnnulus
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyOneResidualAnnulus q) :
    (3 / 25000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hq.1
  have hatom := three_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom
    q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  nlinarith

/-- A `3 / 25000` fourth-trace cap eliminates the order-twenty-one residual annulus. -/
theorem xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_fourthTrace_le
    (hsource : normalizedPrimeArchMoment 1 ≤ 3 / 25000) :
    XiCenteredOrderTwentyOneResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  have hlower :=
    three_over_twentyFiveThousand_lt_source_of_centeredOrderTwentyOneResidualAnnulus q hq
  linarith

/-- The same fourth-trace cap closes centered source moment twenty. -/
theorem normalizedPrimeArchMoment_twenty_pos_of_fourthTrace_le
    (hsource : normalizedPrimeArchMoment 1 ≤ 3 / 25000) :
    0 < normalizedPrimeArchMoment 20 :=
  normalizedPrimeArchMoment_twenty_pos_of_centeredOrderTwentyOneResidualAnnulusEmpty
    (xiCenteredOrderTwentyOneResidualAnnulusEmpty_of_fourthTrace_le hsource)

end

end RHTower
