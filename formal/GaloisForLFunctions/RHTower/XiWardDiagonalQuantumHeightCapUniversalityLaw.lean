import GaloisForLFunctions.RHTower.XiWardEdgeGramSharpLaws
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Xi Ward diagonal quantum height-cap universality

Two independently certified Xi mechanisms confine every strict-right diagonal Ward packet to one
universal open band. Critical-strip geometry gives the strict `8π` lower edge. The strip-edge
spectral budget forces centered height squared above `65`, which turns the second Cauchy channel
into a uniform upper correction smaller than `1/65`.

No Riemann-hypothesis premise, numerical zero table, or new analytic assumption occurs.
-/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

/-- Exact diagonal decomposition into its critical-strip and height-decaying Cauchy channels. -/
theorem xiPairGramTerm_diag_eq (q : XiRightUpperZeroCopy) :
    xiPairGramTerm q q =
      8 * π *
        (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
          ((xiRightCenteredZero q.1).re + 1 / 2) /
            (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
              (xiRightCenteredZero q.1).im ^ 2)) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : (xiRightCenteredZero q.1).re + 1 / 2 ≠ 0 := by
    linarith
  unfold xiPairGramTerm
  field_simp
  ring

/-- The independently certified height floor caps every local diagonal Ward packet. -/
theorem xiPairGramTerm_diag_lt_heightCap (q : XiRightUpperZeroCopy) :
    xiPairGramTerm q q < 8 * π * (131 / 65 : ℝ) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hstrip := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
    linarith
  have hx1 : (xiRightCenteredZero q.1).re + 1 / 2 < 1 := by
    linarith
  have hb := xiWard_offlinePair_height_sq_gt_sixtyfive q
  have hinv :
      1 / ((xiRightCenteredZero q.1).re + 1 / 2) < 2 := by
    rw [div_lt_iff₀ hx]
    nlinarith
  have hden : 0 <
      ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
        (xiRightCenteredZero q.1).im ^ 2 := by
    positivity
  have hsecond :
      ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2) <
        1 / 65 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 65)]
    nlinarith [sq_nonneg ((xiRightCenteredZero q.1).re + 1 / 2)]
  rw [xiPairGramTerm_diag_eq]
  have hadd := add_lt_add hinv hsecond
  have hmul := mul_lt_mul_of_pos_left hadd
    (show 0 < 8 * π by positivity)
  norm_num at hmul ⊢
  exact hmul

/-- **Xi Ward diagonal quantum height-cap universality.** Every strict-right Xi Schwarz pair
contributes a diagonal Ward packet strictly between `8π` and `8π · 131/65`. -/
theorem xiWard_diagonalQuantum_heightCapUniversality
    (q : XiRightUpperZeroCopy) :
    8 * π < xiPairGramTerm q q ∧
      xiPairGramTerm q q < 8 * π * (131 / 65 : ℝ) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hstrip := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
    linarith
  have hx1 : (xiRightCenteredZero q.1).re + 1 / 2 < 1 := by
    linarith
  refine ⟨?_, xiPairGramTerm_diag_lt_heightCap q⟩
  exact lt_of_lt_of_le
    (by
      rw [lt_div_iff₀ hx]
      nlinarith [pi_pos])
    (eightPi_div_le_xiPairGramTerm_diag q)

end

end RHTower
