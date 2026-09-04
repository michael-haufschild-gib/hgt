import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIBlockSchedule

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Number of unit-separated internal Case-II cells at the common source scale. -/
def menonHarmonicCaseIICells (a : ℕ) : ℕ :=
  ⌈(Real.log (a : ℝ)) ^ (200 : ℕ)⌉₊

/-- Paper-scale transition width for a prime block with natural lower endpoint `a`. -/
def menonHarmonicCaseIISmoothingWidth (a : ℕ) : ℝ :=
  (a : ℝ) / (Real.log (a : ℝ)) ^ (20 : ℕ)

/-- Block-uniform line immediately to the right of one. -/
def menonHarmonicCaseIISigma (Y : ℕ) : ℝ :=
  1 + 1 / Real.log (((4 * Y : ℕ) : ℝ) + 1)

/-- Exact Perron budget whose quotient is twice the order-four-hundred reserve. -/
def menonHarmonicCaseIIBudget
    (C0 : ℝ) (a Y : ℕ) : ℝ :=
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let C := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma
  heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma * C *
      (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2)) +
    2 * (cells : ℝ) * C * (Real.log (a : ℝ)) ^ (-300 : ℝ)

theorem menonHarmonicCaseIICells_pos {a : ℕ} (ha : 1 < a) :
    0 < menonHarmonicCaseIICells a := by
  have haR : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [menonHarmonicCaseIICells]
  exact Nat.ceil_pos.2 (by positivity [Real.log_pos haR])

theorem menonHarmonicCaseIISmoothingWidth_pos {a : ℕ} (ha : 1 < a) :
    0 < menonHarmonicCaseIISmoothingWidth a := by
  have haR : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [menonHarmonicCaseIISmoothingWidth]
  positivity [Real.log_pos haR]

theorem menonHarmonicCaseIISigma_gt_one {Y : ℕ} (hY : 0 < Y) :
    1 < menonHarmonicCaseIISigma Y := by
  have harg : (1 : ℝ) < (((4 * Y : ℕ) : ℝ) + 1) := by
    exact_mod_cast (show 1 < 4 * Y + 1 by omega)
  rw [menonHarmonicCaseIISigma]
  exact lt_add_of_pos_right 1 (one_div_pos.mpr (Real.log_pos harg))

theorem menonWideIntervalAmbientKernelMajorant_pos
    {C0 H sigma : ℝ} {X : ℕ} (hC0 : 0 ≤ C0) (hH : 0 < H)
    (hsigma : 0 < sigma) :
    0 < menonWideIntervalAmbientKernelMajorant C0 X H sigma := by
  rw [menonWideIntervalAmbientKernelMajorant]
  positivity

theorem heathBrownWindowRelevantFixedPolylogBound_nonneg
    {L X k : ℕ} {N sigma : ℝ} (hN : 0 < N) :
    0 ≤ heathBrownWindowRelevantFixedPolylogBound L X k N sigma := by
  rw [heathBrownWindowRelevantFixedPolylogBound]
  positivity

theorem menonHarmonicCaseIIBudget_nonneg
    {C0 : ℝ} {a Y : ℕ} (hC0 : 0 ≤ C0) (ha : 1 < a) (hY : 0 < Y) :
    0 ≤ menonHarmonicCaseIIBudget C0 a Y := by
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let C := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma
  have hcells : 0 < cells := menonHarmonicCaseIICells_pos ha
  have hH : 0 < H := menonHarmonicCaseIISmoothingWidth_pos ha
  have hsigma : 1 < sigma := menonHarmonicCaseIISigma_gt_one hY
  have hC : 0 < C := menonWideIntervalAmbientKernelMajorant_pos hC0 hH
    (zero_lt_one.trans hsigma)
  have hP : 0 ≤ heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma :=
    heathBrownWindowRelevantFixedPolylogBound_nonneg (by exact_mod_cast (Nat.zero_lt_of_lt ha))
  have htail : 0 < Real.pi - 2 * Real.arctan ((cells : ℝ) / 2) := by
    linarith [Real.arctan_lt_pi_div_two ((cells : ℝ) / 2)]
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  rw [menonHarmonicCaseIIBudget]
  positivity

theorem menonHarmonicCaseII_quotient_eq
    {C0 : ℝ} {a Y : ℕ} (hC0 : 0 ≤ C0) (ha : 1 < a) (hY : 0 < Y) :
    let cells := menonHarmonicCaseIICells a
    let H := menonHarmonicCaseIISmoothingWidth a
    let sigma := menonHarmonicCaseIISigma Y
    let C := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma
    (menonHarmonicCaseIIBudget C0 a Y -
        heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma * C *
          (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
      ((cells : ℝ) * C) =
        2 * (Real.log (a : ℝ)) ^ (-300 : ℝ) := by
  dsimp only
  have hcells : (menonHarmonicCaseIICells a : ℝ) ≠ 0 := by
    exact_mod_cast (menonHarmonicCaseIICells_pos ha).ne'
  have hH := menonHarmonicCaseIISmoothingWidth_pos ha
  have hsigma := menonHarmonicCaseIISigma_gt_one hY
  have hC : menonWideIntervalAmbientKernelMajorant C0 (4 * Y)
      (menonHarmonicCaseIISmoothingWidth a) (menonHarmonicCaseIISigma Y) ≠ 0 :=
    (menonWideIntervalAmbientKernelMajorant_pos hC0 hH
      (zero_lt_one.trans hsigma)).ne'
  rw [menonHarmonicCaseIIBudget]
  field_simp
  ring

set_option maxHeartbeats 800000 in
theorem exists_absolute_eventually_volume_real_menonFinalRangeBlock_caseII_scheduled_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonTruncatedRangeLadderSteps x),
        ∀ {T : ℝ},
        1 ≤ T → (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 4 ≤ T →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        let a := menonFinalRangeBlockLowerNat x j
        let Y := menonFinalRangeBlockUpperNat x j
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
  filter_upwards [eventually_menonFinalRangeBlock_caseII_endpoints, hbase,
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonTruncatedRangeLadder_basic] with x hx hbaseX hbaseTwo hbasic
  intro j hj T hT hcellsT h2T
  have hend := hx j hj
  rcases hend with ⟨_ha64, haY, hYa⟩
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeBlockUpperNat x j
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let B := menonHarmonicCaseIIBudget C0 a Y
  have hbaseLe : menonFinalRangePrimeCutoffNat x ≤ a := by
    have hbase0 : 0 < menonFinalRangeLadderBase x := by
      rw [menonFinalRangeLadderBase]
      exact_mod_cast (show 0 < menonFinalRangePrimeCutoffNat x by omega)
    have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by
      rcases hbasic with ⟨_, _, _, _, _, heta, _⟩
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
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
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
      have hQeq' := hQeq
      simp only [cells, H, sigma, B] at hQeq'
      rw [hQeq']
      exact hQlt)
  rw [hQeq] at hbound
  simpa only [a, Y, cells, H, sigma, B] using hbound

end

end RHTower.Sieve
