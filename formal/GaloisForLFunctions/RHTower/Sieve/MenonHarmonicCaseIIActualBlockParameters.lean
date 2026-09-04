import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIActualBlock

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

set_option maxHeartbeats 800000 in
theorem exists_absolute_eventually_volume_real_menonFinalRangeActualBlock_caseII_scheduled_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ {T : ℝ},
        1 ≤ T → (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 4 ≤ T →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        let a := menonFinalRangeBlockLowerNat x j
        let Y := menonFinalRangeActualBlockUpperNat x j
        let cells := menonHarmonicCaseIICells a
        let H := menonHarmonicCaseIISmoothingWidth a
        let sigma := menonHarmonicCaseIISigma Y
        let B := menonHarmonicCaseIIBudget C0 a Y
        let Q := 2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        volume.real
            (menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet
              a (4 * Y) Y H B T ((cells : ℝ) / 2)) ≤
          2 * (2 * Real.pi)⁻¹ *
            (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) := by
  obtain ⟨C0, hC0, hcase⟩ :=
    exists_absolute_eventually_volume_real_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_smoothing_le
  rw [eventually_atTop] at hcase
  obtain ⟨a0, hcase⟩ := hcase
  have hbase := tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop a0
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [eventually_menonFinalRangeActualBlock_caseII_endpoints, hbase,
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonFinalRangeLadder_basic] with x hx hbaseX hbaseTwo hbasic
  intro j hj T hT hcellsT h2T
  have hend := hx j hj
  rcases hend with ⟨_ha64, haY, hYa⟩
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let B := menonHarmonicCaseIIBudget C0 a Y
  have hbaseLe : menonFinalRangePrimeCutoffNat x ≤ a := by
    have hbase0 : 0 < menonFinalRangeLadderBase x := by
      rw [menonFinalRangeLadderBase]
      exact_mod_cast (show 0 < menonFinalRangePrimeCutoffNat x by omega)
    have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by
      rcases hbasic with ⟨_, _, _, _, heta, _⟩
      linarith
    have hq : menonFinalRangeLadderBase x ≤
        menonFinalRangeLadderBase x * (1 + menonFinalRangeLadderEta x) ^ j :=
      le_mul_of_one_le_right hbase0.le (one_le_pow₀ hstep)
    change menonFinalRangePrimeCutoffNat x ≤ menonFinalRangeBlockLowerNat x j
    rw [menonFinalRangeBlockLowerNat,
      ← Nat.floor_natCast (R := ℝ) (menonFinalRangePrimeCutoffNat x)]
    exact Nat.floor_mono hq
  have ha0 : a0 ≤ a := hbaseX.trans hbaseLe
  have ha : 1 < a := hbaseTwo.trans hbaseLe
  have hH : 0 < H := menonHarmonicCaseIISmoothingWidth_pos ha
  have hlogOne : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hexp : Real.exp 1 ≤ (a : ℝ) := hexpThree.le.trans haThree
    have hlog := Real.log_le_log (Real.exp_pos 1) hexp
    simpa using hlog
  have hHle : H ≤ 3 * (Y : ℝ) := by
    simp only [H, menonHarmonicCaseIISmoothingWidth]
    have hden : 1 ≤ (Real.log (a : ℝ)) ^ (20 : ℕ) := one_le_pow₀ hlogOne
    have hdiv : (a : ℝ) / (Real.log (a : ℝ)) ^ (20 : ℕ) ≤ (a : ℝ) :=
      div_le_self (Nat.cast_nonneg a) hden
    have haYR : (a : ℝ) ≤ (Y : ℝ) := by exact_mod_cast haY.le
    linarith
  have hsigma : 1 < sigma :=
    menonHarmonicCaseIISigma_gt_one (show 0 < Y by omega)
  have hYpos : 0 < Y := Nat.zero_lt_of_lt haY
  have hB : 0 ≤ B := menonHarmonicCaseIIBudget_nonneg hC0 ha hYpos
  have hcells : 0 < cells := menonHarmonicCaseIICells_pos ha
  have hQeq := menonHarmonicCaseII_quotient_eq
    (C0 := C0) (a := a) (Y := Y) hC0 ha hYpos
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hQlt : (Real.log (a : ℝ)) ^ (-300 : ℝ) <
      2 * (Real.log (a : ℝ)) ^ (-300 : ℝ) := by
    have := Real.rpow_pos_of_pos hlog (-300 : ℝ)
    linarith
  have hbound := hcase a ha0 (Y := Y) (cells := cells) (H := H) (B := B)
    (sigma := sigma) (T := T) (by simpa only [a, Y] using haY)
    (by simpa only [a, Y] using hYa) hH hHle hsigma hB hcells hT
    (by simpa only [cells] using hcellsT) (by simpa only [a] using h2T)
    (by
      rw [hQeq]
      exact hQlt)
  rw [hQeq] at hbound
  simpa only [a, Y, cells, H, sigma, B] using hbound

end

end RHTower.Sieve
