import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIBlockBudget

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- Actual right endpoint of a final-range block, including the terminal clipping. -/
def menonFinalRangeActualBlockUpperNat (x : ℝ) (j : ℕ) : ℕ :=
  min (menonFinalRangeTopNat x) (menonFinalRangeBlockUpperNat x j)

theorem geomBlock_menonFinalRangePrimes_eq_actualBlock
    {x : ℝ} (heta : 0 ≤ menonFinalRangeLadderEta x) (j : ℕ) :
    geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
        (1 + menonFinalRangeLadderEta x) j =
      primesRange (menonFinalRangeBlockLowerNat x j)
        (menonFinalRangeActualBlockUpperNat x j) := by
  ext p
  rw [menonFinalRangePrimes, menonFinalRangeLadderBase,
    mem_geomBlock_primesRange_min heta (by rfl), mem_primesRange]
  rfl

set_option maxHeartbeats 800000 in
theorem eventually_menonFinalRangeActualBlock_caseII_endpoints :
    ∀ᶠ x : ℝ in atTop,
      ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        (64 : ℕ) ^ 8 ≤ menonFinalRangeBlockLowerNat x j ∧
        menonFinalRangeBlockLowerNat x j < menonFinalRangeActualBlockUpperNat x j ∧
        menonFinalRangeActualBlockUpperNat x j ≤
          2 * menonFinalRangeBlockLowerNat x j := by
  have hbaseLarge :=
    tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop ((64 : ℕ) ^ 8 + 2)
  filter_upwards [eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten,
    eventually_inv_menonFinalRangeLadderBase_le_log_rpow_neg_thirty,
    eventually_ge_atTop (Real.exp 2), hbaseLarge] with x hx hetaUpper hinv hxexp hbaseLargeX
  intro j hj
  rcases hx with ⟨hxone, hH, hQ, htop, heta, _hsteps⟩
  let q : ℝ := menonFinalRangeLadderBase x *
    (1 + menonFinalRangeLadderEta x) ^ j
  let a : ℕ := ⌊q⌋₊
  let Y0 : ℕ := ⌊q * (1 + menonFinalRangeLadderEta x)⌋₊
  let Y : ℕ := min (menonFinalRangeTopNat x) Y0
  have hlogTwo : 2 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hxexp
    simpa using h
  have hlog0 : 0 < Real.log x := Real.log_pos hxone
  have hlogOne : 1 ≤ Real.log x := by linarith
  have hbase0 : 0 < menonFinalRangeLadderBase x := by linarith
  have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by linarith
  have hpowStep : 1 ≤ (1 + menonFinalRangeLadderEta x) ^ j := one_le_pow₀ hstep
  have hqBase : menonFinalRangeLadderBase x ≤ q := by
    dsimp only [q]
    nlinarith [mul_le_mul_of_nonneg_left hpowStep hbase0.le]
  have hq0 : 0 < q := lt_of_lt_of_le hbase0 hqBase
  have haBase : menonFinalRangePrimeCutoffNat x ≤ a := by
    rw [← Nat.floor_natCast (R := ℝ) (menonFinalRangePrimeCutoffNat x)]
    exact Nat.floor_mono hqBase
  have haLarge : (64 : ℕ) ^ 8 ≤ a := by omega
  have hpow30pos : 0 < (Real.log x) ^ (30 : ℕ) := pow_pos hlog0 _
  have hbaseLower : (Real.log x) ^ (30 : ℕ) ≤ menonFinalRangeLadderBase x := by
    have hpEq : (Real.log x) ^ (30 : ℝ) = (Real.log x) ^ (30 : ℕ) :=
      Real.rpow_natCast _ 30
    have hinv' : (menonFinalRangeLadderBase x)⁻¹ ≤
        ((Real.log x) ^ (30 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hlog0.le, hpEq] at hinv
      simpa only [one_div] using hinv
    exact (inv_le_inv₀ hbase0 hpow30pos).mp hinv'
  have hetaLower : 1 / menonFinalRangeLadderH x ≤ menonFinalRangeLadderEta x := by
    have he := Real.add_one_le_exp (1 / menonFinalRangeLadderH x)
    rw [menonFinalRangeLadderEta]
    linarith
  have hpowTenPos : 0 < (Real.log x) ^ (10 : ℕ) := pow_pos hlog0 _
  have hpowTwenty : 1 < (Real.log x) ^ (20 : ℕ) :=
    one_lt_pow₀ (lt_of_lt_of_le one_lt_two hlogTwo) (by norm_num)
  have hbaseDiv : 1 < menonFinalRangeLadderBase x *
      (1 / menonFinalRangeLadderH x) := by
    rw [menonFinalRangeLadderH]
    calc
      1 < (Real.log x) ^ (20 : ℕ) := hpowTwenty
      _ = (Real.log x) ^ (30 : ℕ) * (1 / (Real.log x) ^ (10 : ℕ)) := by
        field_simp
      _ ≤ menonFinalRangeLadderBase x * (1 / (Real.log x) ^ (10 : ℕ)) :=
        mul_le_mul_of_nonneg_right hbaseLower (by positivity)
  have hqEta : 1 < q * menonFinalRangeLadderEta x := by
    exact hbaseDiv.trans_le
      (mul_le_mul hqBase hetaLower (by positivity) hq0.le)
  have haCastLe : (a : ℝ) ≤ q := by
    dsimp only [a]
    exact Nat.floor_le hq0.le
  have haLtY0 : a < Y0 := by
    have haOneLe : ((a + 1 : ℕ) : ℝ) ≤
        q * (1 + menonFinalRangeLadderEta x) := by
      push_cast
      nlinarith
    have : a + 1 ≤ Y0 := by
      dsimp only [Y0]
      exact Nat.le_floor haOneLe
    omega
  have hjlt : j < menonFinalRangeLadderSteps x := Finset.mem_range.1 hj
  have hqTop : q < (menonFinalRangeTopNat x : ℝ) := by
    dsimp only [q]
    rw [menonFinalRangeLadder_pow_eq_exp]
    exact geometric_before_ceil_depth_lt hH hbase0 htop hjlt
  have haLtTop : a < menonFinalRangeTopNat x := by
    have : (a : ℝ) < (menonFinalRangeTopNat x : ℝ) := haCastLe.trans_lt hqTop
    exact_mod_cast this
  have haLtY : a < Y := by
    dsimp only [Y]
    exact lt_min haLtTop haLtY0
  have hpowTenFour : (4 : ℝ) ≤ (Real.log x) ^ (10 : ℕ) := by
    have hsq : (4 : ℝ) ≤ (Real.log x) ^ (2 : ℕ) := by nlinarith
    have hpowNonneg : 0 ≤ (Real.log x) ^ (8 : ℕ) := by positivity
    calc
      (4 : ℝ) ≤ (Real.log x) ^ (2 : ℕ) := hsq
      _ ≤ (Real.log x) ^ (2 : ℕ) * (Real.log x) ^ (8 : ℕ) := by
        nlinarith [one_le_pow₀ hlogOne (n := 8)]
      _ = (Real.log x) ^ (10 : ℕ) := by ring
  have hetaHalf : menonFinalRangeLadderEta x ≤ (1 : ℝ) / 2 := by
    calc
      menonFinalRangeLadderEta x ≤ 2 / (Real.log x) ^ (10 : ℕ) := hetaUpper.2.1
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hpowTenPos]
        nlinarith
  have hqLtFloor : q < (a : ℝ) + 1 := by
    dsimp only [a]
    exact Nat.lt_floor_add_one q
  have hY0lt : Y0 < 2 * a + 1 := by
    apply (Nat.floor_lt (mul_nonneg hq0.le (by linarith : 0 ≤ 1 + menonFinalRangeLadderEta x))).2
    push_cast
    have haOne : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      q * (1 + menonFinalRangeLadderEta x) ≤ q * (3 / 2 : ℝ) := by
        gcongr
        linarith
      _ < ((a : ℝ) + 1) * (3 / 2 : ℝ) := by gcongr
      _ ≤ 2 * (a : ℝ) + 1 := by nlinarith
  have hY : Y ≤ 2 * a := by
    have : Y ≤ Y0 := min_le_right _ _
    omega
  have hUpper : menonFinalRangeActualBlockUpperNat x j = Y := by
    rw [menonFinalRangeActualBlockUpperNat]
    congr 1
    dsimp only [Y0, q, menonFinalRangeBlockUpperNat]
    rw [pow_succ]
    congr 1
    ring
  rw [hUpper]
  simpa only [a, q, menonFinalRangeBlockLowerNat] using
    And.intro haLarge (And.intro haLtY hY)

end

end RHTower.Sieve
