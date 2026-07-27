import GaloisForLFunctions.RHTower.XiOrderSeventeenEdgeCorner

/-!
# Source exclusion of the order-seventeen compact edge corner

The order-eighteen sector can fail only in

`4/25 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 132`.

The seven-interval theta floor bounds the complete nonnegative fourth reciprocal trace below
`1/5000`. Four FE--Schwarz copies of any zero in this corner would contribute more than
`1/5000`, excluding the corner unconditionally and without a zero table.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One fourth reciprocal-trace atom in the order-seventeen compact edge corner exceeds one
quarter of the global source threshold. -/
theorem five_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderSeventeen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 132) :
    (5 / 100000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 529 / 4
  have hu0 : 0 < u := by
    exact (by norm_num : (0 : ℝ) < 4 / 25).trans
      (by simpa only [u] using huLower)
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 132 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ 2 < W ^ 2 := by
    exact (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsecond : 0 < 5 * (W ^ 2 + w ^ 2) - 100000 := by
    have hsqLower : (85 : ℝ) ^ 2 < w ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      100000 * w ^ 2 - 5 * w ^ 4 >
        100000 * W ^ 2 - 5 * W ^ 4 := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (100000 * w ^ 2 - 5 * w ^ 4) -
            (100000 * W ^ 2 - 5 * W ^ 4) =
          (W ^ 2 - w ^ 2) * (5 * (W ^ 2 + w ^ 2) - 100000) := by
      ring
    nlinarith
  have huv : u * v < 33 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right (by simpa only [u] using huUpper) hv0
      _ < (1 / 4 : ℝ) * 132 :=
        mul_lt_mul_of_pos_left (by simpa only [v] using hvUpper) (by norm_num)
      _ = 33 := by norm_num
  have hendpoint :
      0 < (100000 * W ^ 2 - 5 * W ^ 4) - 800000 * 33 := by
    norm_num [W]
  have hG :
      0 < 100000 * (v ^ 2 - 6 * u * v + u ^ 2) - 5 * w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    have hshapeShift :
        100000 * W ^ 2 - 5 * W ^ 4 - 800000 * 33 <
          100000 * w ^ 2 - 5 * w ^ 4 - 800000 * 33 := by
      have h := add_lt_add_right hshape (-800000 * 33)
      convert h using 1 <;> ring
    have hbase : 0 < 100000 * w ^ 2 - 5 * w ^ 4 - 800000 * 33 :=
      hendpoint.trans hshapeShift
    have huvScaled : 800000 * (u * v) < 800000 * 33 :=
      mul_lt_mul_of_pos_left huv (by norm_num)
    have huvShift :
        100000 * w ^ 2 - 5 * w ^ 4 - 800000 * 33 <
          100000 * w ^ 2 - 5 * w ^ 4 - 800000 * (u * v) := by
      exact sub_lt_sub_left huvScaled _
    have htarget : 0 < 100000 * w ^ 2 - 5 * w ^ 4 - 800000 * (u * v) :=
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

/-- Four distinct FE--Schwarz copies of an order-seventeen corner zero overspend the complete
fourth reciprocal trace. -/
theorem one_over_fiveThousand_lt_source_of_orderSeventeen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 132) :
    (1 / 5000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    rw [h] at huLower
    norm_num at huLower
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := four_mul_le_tsum_of_quartet_invariant
    xiFourthReciprocalTraceAtom_nonneg hsum
    xiFourthReciprocalTraceAtom_lineConj xiFourthReciprocalTraceAtom_conj q hoff
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
  have hatom :=
    five_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderSeventeen_edgeCorner
      q huLower huUpper hvLower hvUpper
  nlinarith

/-- **Unconditional order-seventeen compact-corner exclusion.** -/
theorem not_exists_xiZeroCopy_mem_orderSeventeen_edgeCorner :
    ¬ ∃ q : XiZeroCopy,
      (4 / 25 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 132 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hlower := one_over_fiveThousand_lt_source_of_orderSeventeen_edgeCorner
    q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_one_over_fiveThousand
  linarith

/-- The order-seventeen squared-seam source has strict positive atomwise sign everywhere. -/
theorem xiOrderEighteenReciprocalPower_re_pos
    (q : XiZeroCopy) {y : ℝ} (hy : 1 / 4 < y) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 18).re := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      nlinarith [sq_nonneg (q.1 : ℂ).im]
    apply orderEighteenReciprocalPower_re_pos_of_sectorRatio hA
    rw [hoff]
    norm_num
    exact sq_pos_of_pos hA
  · by_contra hnot
    have hcorner := xiOrderEighteenReciprocalPower_nonpos_mem_edgeCorner q hoff hy
      (le_of_not_gt hnot)
    exact not_exists_xiZeroCopy_mem_orderSeventeen_edgeCorner ⟨q, hcorner⟩

end

end RHTower
