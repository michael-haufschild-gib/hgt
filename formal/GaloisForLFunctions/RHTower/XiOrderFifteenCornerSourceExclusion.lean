import GaloisForLFunctions.RHTower.XiOrderFifteenEdgeCorner

/-!
# Source exclusion of the order-fifteen compact edge corner

The order-sixteen squared-Xi sector can fail only in the compact corner

`1/5 < (Re rho - 1/2)^(2 : ℕ) < 1/4`, `85 < (Im rho)^(2 : ℕ) < 104`.

The sharpened theta floor and endpoint-curvature budget bound the complete nonnegative fourth
reciprocal trace below `9/25000`.  Four FE--Schwarz copies of any zero in this corner would
contribute more than `9/25000`, excluding the corner unconditionally and without a zero table.

This closes the next fixed squared-seam order; it is a route discriminator, not an RH disproof.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One reciprocal fourth-trace atom in the order-fifteen compact edge corner exceeds one quarter
of the sharpened global source threshold. -/
theorem nine_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderFifteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 104) :
    (9 / 100000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let w : ℝ := u + v
  let W : ℝ := 417 / 4
  have hu0 : 0 < u := by
    exact (by norm_num : (0 : ℝ) < 1 / 5).trans
      (by simpa only [u] using huLower)
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 104 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ (2 : ℕ) < W ^ (2 : ℕ) := by
    exact (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsecond : 0 < 9 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 100000 := by
    have hsqLower : (85 : ℝ) ^ (2 : ℕ) < w ^ (2 : ℕ) :=
      (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      100000 * w ^ (2 : ℕ) - 9 * w ^ (4 : ℕ) >
        100000 * W ^ (2 : ℕ) - 9 * W ^ (4 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (100000 * w ^ (2 : ℕ) - 9 * w ^ (4 : ℕ)) -
            (100000 * W ^ (2 : ℕ) - 9 * W ^ (4 : ℕ)) =
          (W ^ (2 : ℕ) - w ^ (2 : ℕ)) * (9 * (W ^ (2 : ℕ) + w ^ (2 : ℕ)) - 100000) := by
      ring
    nlinarith
  have huv : u * v < 26 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right (by simpa only [u] using huUpper) hv0
      _ < (1 / 4 : ℝ) * 104 :=
        mul_lt_mul_of_pos_left (by simpa only [v] using hvUpper) (by norm_num)
      _ = 26 := by norm_num
  have hendpoint :
      0 < (100000 * W ^ (2 : ℕ) - 9 * W ^ (4 : ℕ)) - 800000 * 26 := by
    norm_num [W]
  have hG :
      0 < 100000 * (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) - 9 * w ^ (4 : ℕ) := by
    have hN : v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ) = w ^ (2 : ℕ) - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ (2 : ℕ)).re =
        (v ^ (2 : ℕ) - 6 * u * v + u ^ (2 : ℕ)) / w ^ (4 : ℕ) := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 100000) (pow_pos hw0 4)]
  nlinarith

/-- Four distinct FE--Schwarz copies of an order-fifteen corner zero would overspend the complete
fourth reciprocal trace. -/
theorem nine_over_twentyFiveThousand_lt_source_of_orderFifteen_edgeCorner
    (q : XiZeroCopy)
    (huLower : (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ))
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ (2 : ℕ))
    (hvUpper : (q.1 : ℂ).im ^ (2 : ℕ) < 104) :
    (9 / 25000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 :=
    re_ne_half_of_pos_centered_sq (by linarith)
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ (2 : ℕ)).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := four_mul_le_tsum_of_quartet_invariant
    xiFourthReciprocalTraceAtom_nonneg hsum
    xiFourthReciprocalTraceAtom_lineConj xiFourthReciprocalTraceAtom_conj q hoff
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
  have hatom :=
    nine_over_oneHundredThousand_lt_xiFourthReciprocalTraceAtom_of_orderFifteen_edgeCorner
      q huLower huUpper hvLower hvUpper
  nlinarith

/-- **Unconditional order-fifteen compact-corner exclusion.** -/
theorem not_exists_xiZeroCopy_mem_orderFifteen_edgeCorner :
    ¬ ∃ q : XiZeroCopy,
      (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ (2 : ℕ) ∧
      (q.1 : ℂ).im ^ (2 : ℕ) < 104 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hlower := nine_over_twentyFiveThousand_lt_source_of_orderFifteen_edgeCorner
    q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_twentyFiveThousand
  linarith

/-- The order-fifteen squared-seam source has strict positive atomwise sign everywhere. -/
theorem xiOrderSixteenReciprocalPower_re_pos
    (q : XiZeroCopy) {y : ℝ} (hy : 1 / 4 < y) :
    let A : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ (16 : ℕ)).re :=
  xiZeroCopy_reciprocalPower_re_pos_of_window_empty q hy
    (fun _ _ hA h => orderSixteenReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hnonpos => xiOrderSixteenReciprocalPower_nonpos_mem_edgeCorner q hoff hy hnonpos)
    (fun hc => not_exists_xiZeroCopy_mem_orderFifteen_edgeCorner ⟨q, hc⟩)

end

end RHTower
