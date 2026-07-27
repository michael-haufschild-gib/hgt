import GaloisForLFunctions.RHTower.XiOrderEighteenEdgeCorner

/-!
# Source exclusion of the order-eighteen compact edge corner

The order-nineteen sector can fail only in

`7/50 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 147`.

The sharpened seven-interval theta floor bounds the complete nonnegative fourth reciprocal trace
below `9/50000`. Four FE--Schwarz copies of any zero in this corner would contribute more than
`9/50000`, excluding the corner unconditionally and without a zero table.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One fourth reciprocal-trace atom in the order-eighteen compact edge corner exceeds one
quarter of the global source threshold. -/
theorem nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderEighteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 147) :
    (9 / 200000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re :=
  nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_below_2365_over_16 q
    (by linarith) huUpper hvLower (by linarith)

/-- Four distinct FE--Schwarz copies of an order-eighteen corner zero overspend the complete
fourth reciprocal trace. -/
theorem nine_over_fiftyThousand_lt_source_of_orderEighteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 147) :
    (9 / 50000 : ℝ) < normalizedPrimeArchMoment 1 := by
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
    nine_over_twoHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderEighteen_edgeCorner
      q huLower huUpper hvLower hvUpper
  nlinarith

/-- **Unconditional order-eighteen compact-corner exclusion.** -/
theorem not_exists_xiZeroCopy_mem_orderEighteen_edgeCorner :
    ¬ ∃ q : XiZeroCopy,
      (7 / 50 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 147 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hlower := nine_over_fiftyThousand_lt_source_of_orderEighteen_edgeCorner
    q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand
  linarith

/-- The order-eighteen squared-seam source has strict positive atomwise sign everywhere. -/
theorem xiOrderNineteenReciprocalPower_re_pos
    (q : XiZeroCopy) {y : ℝ} (hy : 1 / 4 < y) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 19).re := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      nlinarith [sq_nonneg (q.1 : ℂ).im]
    apply orderNineteenReciprocalPower_re_pos_of_sectorRatio hA
    rw [hoff]
    norm_num
    exact sq_pos_of_pos hA
  · by_contra hnot
    have hcorner := xiOrderNineteenReciprocalPower_nonpos_mem_edgeCorner q hoff hy
      (le_of_not_gt hnot)
    exact not_exists_xiZeroCopy_mem_orderEighteen_edgeCorner ⟨q, hcorner⟩

end

end RHTower
