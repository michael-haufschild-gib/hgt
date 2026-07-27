import GaloisForLFunctions.RHTower.XiOrderSixteenEdgeCorner

/-!
# Source exclusion of the order-sixteen compact edge corner

The order-seventeen squared-Xi sector can fail only in the compact corner

`9/50 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 118`.

The six-interval theta floor and endpoint-curvature budget bound the complete nonnegative fourth
reciprocal trace below `7/25000`.  Four FE--Schwarz copies of any zero in this corner would
contribute more than `7/25000`, excluding the corner unconditionally and without a zero table.

This closes the next fixed squared-seam order; it is a route discriminator, not an RH disproof.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One reciprocal fourth-trace atom in the order-sixteen compact edge corner exceeds one quarter
of the global source threshold. -/
theorem seven_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderSixteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 118) :
    (7 / 100000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 473 / 4
  have hu0 : 0 < u := by
    exact (by norm_num : (0 : ℝ) < 9 / 50).trans
      (by simpa only [u] using huLower)
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 118 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ 2 < W ^ 2 := by
    exact (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsecond : 0 < 7 * (W ^ 2 + w ^ 2) - 100000 := by
    have hsqLower : (85 : ℝ) ^ 2 < w ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      100000 * w ^ 2 - 7 * w ^ 4 >
        100000 * W ^ 2 - 7 * W ^ 4 := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (100000 * w ^ 2 - 7 * w ^ 4) -
            (100000 * W ^ 2 - 7 * W ^ 4) =
          (W ^ 2 - w ^ 2) * (7 * (W ^ 2 + w ^ 2) - 100000) := by
      ring
    nlinarith
  have huv : u * v < 59 / 2 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right (by simpa only [u] using huUpper) hv0
      _ < (1 / 4 : ℝ) * 118 :=
        mul_lt_mul_of_pos_left (by simpa only [v] using hvUpper) (by norm_num)
      _ = 59 / 2 := by norm_num
  have hendpoint :
      0 < (100000 * W ^ 2 - 7 * W ^ 4) - 800000 * (59 / 2) := by
    norm_num [W]
  have hG :
      0 < 100000 * (v ^ 2 - 6 * u * v + u ^ 2) - 7 * w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    have hshapeShift :
        100000 * W ^ 2 - 7 * W ^ 4 - 800000 * (59 / 2) <
          100000 * w ^ 2 - 7 * w ^ 4 - 800000 * (59 / 2) := by
      have h := add_lt_add_right hshape (-800000 * (59 / 2))
      convert h using 1 <;> ring
    have hbase :
        0 < 100000 * w ^ 2 - 7 * w ^ 4 - 800000 * (59 / 2) := by
      exact hendpoint.trans hshapeShift
    have huvScaled : 800000 * (u * v) < 800000 * (59 / 2) :=
      mul_lt_mul_of_pos_left huv (by norm_num)
    have huvShift :
        100000 * w ^ 2 - 7 * w ^ 4 - 800000 * (59 / 2) <
          100000 * w ^ 2 - 7 * w ^ 4 - 800000 * (u * v) := by
      exact sub_lt_sub_left huvScaled _
    have htarget :
        0 < 100000 * w ^ 2 - 7 * w ^ 4 - 800000 * (u * v) :=
      hbase.trans huvShift
    rw [hN]
    convert htarget using 1 <;> ring
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ 2).re =
        (v ^ 2 - 6 * u * v + u ^ 2) / w ^ 4 := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 100000) (pow_pos hw0 4)]
  nlinarith

/-- Four distinct FE--Schwarz copies of an order-sixteen corner zero would overspend the complete
fourth reciprocal trace. -/
theorem seven_over_twentyFiveThousand_lt_source_of_orderSixteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 118) :
    (7 / 25000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 :=
    re_ne_half_of_pos_centered_sq (by linarith)
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := four_mul_le_tsum_of_quartet_invariant
    xiFourthReciprocalTraceAtom_nonneg hsum
    xiFourthReciprocalTraceAtom_lineConj xiFourthReciprocalTraceAtom_conj q hoff
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
  have hatom :=
    seven_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderSixteen_edgeCorner
      q huLower huUpper hvLower hvUpper
  nlinarith

/-- **Unconditional order-sixteen compact-corner exclusion.** -/
theorem not_exists_xiZeroCopy_mem_orderSixteen_edgeCorner :
    ¬ ∃ q : XiZeroCopy,
      (9 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 118 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hlower := seven_over_twentyFiveThousand_lt_source_of_orderSixteen_edgeCorner
    q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_seven_over_twentyFiveThousand
  linarith

/-- The order-sixteen squared-seam source has strict positive atomwise sign everywhere. -/
theorem xiOrderSeventeenReciprocalPower_re_pos
    (q : XiZeroCopy) {y : ℝ} (hy : 1 / 4 < y) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 17).re :=
  xiZeroCopy_reciprocalPower_re_pos_of_window_empty q hy
    (fun _ _ hA h => orderSeventeenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hnonpos => xiOrderSeventeenReciprocalPower_nonpos_mem_edgeCorner q hoff hy hnonpos)
    (fun hc => not_exists_xiZeroCopy_mem_orderSixteen_edgeCorner ⟨q, hc⟩)

end

end RHTower
