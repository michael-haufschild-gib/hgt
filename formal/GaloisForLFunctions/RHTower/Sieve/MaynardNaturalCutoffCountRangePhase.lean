import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCutoffSchedule

namespace RHTower.Sieve

/-- Existing count ceiling is strictly below the universal natural-cutoff low-cell threshold. -/
theorem routeT_currentCountCeiling_lt_naturalCutoffLowCellThreshold :
    (19 / 9 : ℝ) < 24 / 11 := by
  norm_num

/-- Any strict-gap split compatible with the natural cutoff leaves the untreated low-cell phase
strictly above the critical `3/2` wall when the selected-count ceiling remains `19/9`. -/
theorem routeT_naturalCutoff_lowCell_phase_wall_currentCount
    {theta : ℝ} (htheta : 3 / 8 ≤ theta) :
    3 / 2 < -1 + 3 * theta + 3 / (19 / 9 : ℝ) := by
  norm_num at htheta ⊢
  linarith

/-- More generally, a subcritical untreated low-cell phase together with the natural-cutoff
constraint forces the selected-count ceiling strictly past `24/11`. -/
theorem routeT_countCeiling_gt_twentyFourElevenths_of_naturalCutoff_lowCell_subcritical
    {theta mu : ℝ} (htheta : 3 / 8 ≤ theta) (hmu : 0 < mu)
    (hcritical : -1 + 3 * theta + 3 / mu < 3 / 2) :
    24 / 11 < mu := by
  have hfrac : 3 / mu < 11 / 8 := by
    linarith
  have hmul : 3 < (11 / 8 : ℝ) * mu := (div_lt_iff₀ hmu).mp hfrac
  norm_num at hmul ⊢
  linarith

/-- Exact reason the order-50 schedule cannot close untreated low cells at the corpus count
ceiling: its exponent exceeds `3/2` by `127/1520`. -/
theorem routeT_orderFifty_currentCount_lowCell_phase_exact :
    -1 + 3 * (31 / 80 : ℝ) + 3 / (19 / 9 : ℝ) =
      3 / 2 + 127 / 1520 := by
  norm_num

/-- The order-500 split has exact natural-cutoff tail reserve `T^(-1/500)`. -/
theorem routeT_orderFiveHundred_naturalCutoff_tail_exponent_exact :
    (8 / 5 : ℝ) * (1 - 301 / 800) * 501 - 500 = -1 / 500 := by
  norm_num

/-- Small gaps at the order-500 split remain strictly below the critical prefix exponent. -/
theorem routeT_orderFiveHundred_smallGap_prefix_subcritical :
    1 + (301 / 800 : ℝ) < 3 / 2 := by
  norm_num

/-- Raising the count ceiling to `11/5` crosses the universal threshold. -/
theorem routeT_twentyFourElevenths_lt_orderFiveHundred_countCeiling :
    (24 / 11 : ℝ) < 11 / 5 := by
  norm_num

/-- At count ceiling `11/5`, the order-500 untreated low-cell phase lands below `3/2` with exact
reserve `67/8800`. -/
theorem routeT_orderFiveHundred_lowCell_phase_exact :
    -1 + 3 * (301 / 800 : ℝ) + 3 / (11 / 5 : ℝ) =
      3 / 2 - 67 / 8800 := by
  norm_num

theorem routeT_orderFiveHundred_lowCell_phase_subcritical :
    -1 + 3 * (301 / 800 : ℝ) + 3 / (11 / 5 : ℝ) < 3 / 2 := by
  rw [routeT_orderFiveHundred_lowCell_phase_exact]
  norm_num

end RHTower.Sieve
