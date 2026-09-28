import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardTwoPrimeDensity

/-!
# Two-prime-cofactor section: strip bounds for `2/11 ≤ α₂ ≤ 0.205`

For each strip `[a, b]` of the `α₂`-range, the kernel integrals `∫₁^{B} log β/((1+β)(1-(2+β)c)) dβ`
at `c = a, b` are bounded on `β`-cells of width `1/10` by the tangent of `log` and the chords of
the two reciprocals; the section is then below the affine strip envelope, whose integral against
`dα₂/α₂` is bounded through the chord of `1/α₂`.  Parameter `κ = 10⁻⁶`.
-/

namespace RHTower.Sieve

open Real intervalIntegral

noncomputable section

theorem harmanTwoPrimeKernel_cell_0_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (2 / 11) β ≤ 5340467 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (2 / 11) β ≤ 3805889 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (2 / 11) β ≤ 24262723 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (2 / 11) β ≤ 32698237 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (2 / 11) β ≤ 8145667 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (2 / 11) β ≤ 12131063 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (2 / 11) β ≤ 11248319 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (2 / 11) β ≤ 32014873 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_8 :
    ∫ β in (9 / 5 : ℝ)..(19 / 10), harmanTwoPrimeKernel (2 / 11) β ≤ 36020273 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 9 / 5)
      (c₂ := 19 / 10) (m := 37 / 20) (U := logUpper 0 (37 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_9 :
    ∫ β in (19 / 10 : ℝ)..(2), harmanTwoPrimeKernel (2 / 11) β ≤ 80437301 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 19 / 10)
      (c₂ := 2) (m := 39 / 20) (U := logUpper 0 (39 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_a_10 :
    ∫ β in (2 : ℝ)..(((3 / 4 + 1 / 1000000) / (65 / 352) - 2)), harmanTwoPrimeKernel (2 / 11) β ≤ 5388047 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 2 / 11) (c₁ := 2)
      (c₂ := ((3 / 4 + 1 / 1000000) / (65 / 352) - 2)) (m := 8250011 / 4062500) (U := logUpper 1 (8250011 / 4062500))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 1 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_0_a :
    ∫ β in (1 : ℝ)..((3 / 4 + 1 / 1000000) / (65 / 352) - 2), harmanTwoPrimeKernel (2 / 11) β ≤ 123351807 / 250000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (2 / 11)) (Set.Icc 1 ((3 / 4 + 1 / 1000000) / (65 / 352) - 2)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ (3 / 4 + 1 / 1000000) / (65 / 352) - 2 →
      IntervalIntegrable (harmanTwoPrimeKernel (2 / 11)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (9 / 5) (19 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (19 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (19 / 10) (2) (by norm_num) (by norm_num) (by norm_num))
      (ii (2) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_0_a_0, harmanTwoPrimeKernel_cell_0_a_1, harmanTwoPrimeKernel_cell_0_a_2, harmanTwoPrimeKernel_cell_0_a_3, harmanTwoPrimeKernel_cell_0_a_4, harmanTwoPrimeKernel_cell_0_a_5, harmanTwoPrimeKernel_cell_0_a_6, harmanTwoPrimeKernel_cell_0_a_7, harmanTwoPrimeKernel_cell_0_a_8, harmanTwoPrimeKernel_cell_0_a_9, harmanTwoPrimeKernel_cell_0_a_10]

theorem harmanTwoPrimeKernel_cell_0_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 5447837 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 15550943 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 2482507 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 16758387 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (65 / 352) β ≤ 41831489 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 49949057 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 58035751 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 66254561 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_8 :
    ∫ β in (9 / 5 : ℝ)..(19 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 9346889 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 9 / 5)
      (c₂ := 19 / 10) (m := 37 / 20) (U := logUpper 0 (37 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_9 :
    ∫ β in (19 / 10 : ℝ)..(2), harmanTwoPrimeKernel (65 / 352) β ≤ 83784507 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 19 / 10)
      (c₂ := 2) (m := 39 / 20) (U := logUpper 0 (39 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_0_b_10 :
    ∫ β in (2 : ℝ)..(((3 / 4 + 1 / 1000000) / (65 / 352) - 2)), harmanTwoPrimeKernel (65 / 352) β ≤ 56296967 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 2)
      (c₂ := ((3 / 4 + 1 / 1000000) / (65 / 352) - 2)) (m := 8250011 / 4062500) (U := logUpper 1 (8250011 / 4062500))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 1 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_0_b :
    ∫ β in (1 : ℝ)..((3 / 4 + 1 / 1000000) / (65 / 352) - 2), harmanTwoPrimeKernel (65 / 352) β ≤ 127567017 / 250000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (65 / 352)) (Set.Icc 1 ((3 / 4 + 1 / 1000000) / (65 / 352) - 2)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ (3 / 4 + 1 / 1000000) / (65 / 352) - 2 →
      IntervalIntegrable (harmanTwoPrimeKernel (65 / 352)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (9 / 5) (19 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (19 / 10) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (19 / 10) (2) (by norm_num) (by norm_num) (by norm_num))
      (ii (2) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_0_b_0, harmanTwoPrimeKernel_cell_0_b_1, harmanTwoPrimeKernel_cell_0_b_2, harmanTwoPrimeKernel_cell_0_b_3, harmanTwoPrimeKernel_cell_0_b_4, harmanTwoPrimeKernel_cell_0_b_5, harmanTwoPrimeKernel_cell_0_b_6, harmanTwoPrimeKernel_cell_0_b_7, harmanTwoPrimeKernel_cell_0_b_8, harmanTwoPrimeKernel_cell_0_b_9, harmanTwoPrimeKernel_cell_0_b_10]

theorem harmanDiscardTwoPrimeSection_le_strip_0 :
    ∀ x ∈ Set.Icc (2 / 11 : ℝ) (65 / 352), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (2 / 11) (65 / 352) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (3 / 4 + 1 / 1000000) (123351807 / 250000000) (127567017 / 250000000)
        (logUpper 1 ((3 / 4 + 1 / 1000000) / (65 / 352) - 2 + (3 / 4 + 1 / 1000000) * (1 / (2 / 11) - 1 / (65 / 352)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_one (by norm_num) (by norm_num) (by norm_num))
    (log_le_logUpper 1 (by norm_num)) harmanTwoPrimeKernel_integral_0_a
    harmanTwoPrimeKernel_integral_0_b

theorem harmanTwoPrimeStripEnvelope_integral_0 :
    ∫ x in (2 / 11 : ℝ)..(65 / 352),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (2 / 11) (65 / 352) ((3 / 4 + 1 / 1000000) / (65 / 352) - 2) (3 / 4 + 1 / 1000000) (123351807 / 250000000) (127567017 / 250000000)
        (logUpper 1 ((3 / 4 + 1 / 1000000) / (65 / 352) - 2 + (3 / 4 + 1 / 1000000) * (1 / (2 / 11) - 1 / (65 / 352)))) x / x ≤ 1658137 / 200000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 5447837 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 15550943 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 2482507 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 16758387 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (65 / 352) β ≤ 41831489 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 49949057 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 58035751 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (65 / 352) β ≤ 66254561 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_8 :
    ∫ β in (9 / 5 : ℝ)..(19 / 10), harmanTwoPrimeKernel (65 / 352) β ≤ 9346889 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 9 / 5)
      (c₂ := 19 / 10) (m := 37 / 20) (U := logUpper 0 (37 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_9 :
    ∫ β in (19 / 10 : ℝ)..(2), harmanTwoPrimeKernel (65 / 352) β ≤ 83784507 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 19 / 10)
      (c₂ := 2) (m := 39 / 20) (U := logUpper 0 (39 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_a_10 :
    ∫ β in (2 : ℝ)..(((3 / 4 + 1 / 1000000) / (3 / 16) - 2)), harmanTwoPrimeKernel (65 / 352) β ≤ 943 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 65 / 352) (c₁ := 2)
      (c₂ := ((3 / 4 + 1 / 1000000) / (3 / 16) - 2)) (m := 750001 / 375000) (U := logUpper 1 (750001 / 375000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 1 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_1_a :
    ∫ β in (1 : ℝ)..((3 / 4 + 1 / 1000000) / (3 / 16) - 2), harmanTwoPrimeKernel (65 / 352) β ≤ 56746977 / 125000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (65 / 352)) (Set.Icc 1 ((3 / 4 + 1 / 1000000) / (3 / 16) - 2)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ (3 / 4 + 1 / 1000000) / (3 / 16) - 2 →
      IntervalIntegrable (harmanTwoPrimeKernel (65 / 352)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (9 / 5) (19 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (19 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (19 / 10) (2) (by norm_num) (by norm_num) (by norm_num))
      (ii (2) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_1_a_0, harmanTwoPrimeKernel_cell_1_a_1, harmanTwoPrimeKernel_cell_1_a_2, harmanTwoPrimeKernel_cell_1_a_3, harmanTwoPrimeKernel_cell_1_a_4, harmanTwoPrimeKernel_cell_1_a_5, harmanTwoPrimeKernel_cell_1_a_6, harmanTwoPrimeKernel_cell_1_a_7, harmanTwoPrimeKernel_cell_1_a_8, harmanTwoPrimeKernel_cell_1_a_9, harmanTwoPrimeKernel_cell_1_a_10]

theorem harmanTwoPrimeKernel_cell_1_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 2779809 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 7946371 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 25414143 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 8594353 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (3 / 16) β ≤ 42996169 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 6432527 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 59948371 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 536249 / 7812500 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_8 :
    ∫ β in (9 / 5 : ℝ)..(19 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 77725939 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 9 / 5)
      (c₂ := 19 / 10) (m := 37 / 20) (U := logUpper 0 (37 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_9 :
    ∫ β in (19 / 10 : ℝ)..(2), harmanTwoPrimeKernel (3 / 16) β ≤ 21855767 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 19 / 10)
      (c₂ := 2) (m := 39 / 20) (U := logUpper 0 (39 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_1_b_10 :
    ∫ β in (2 : ℝ)..(((3 / 4 + 1 / 1000000) / (3 / 16) - 2)), harmanTwoPrimeKernel (3 / 16) β ≤ 493 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 2)
      (c₂ := ((3 / 4 + 1 / 1000000) / (3 / 16) - 2)) (m := 750001 / 375000) (U := logUpper 1 (750001 / 375000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 1 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_1_b :
    ∫ β in (1 : ℝ)..((3 / 4 + 1 / 1000000) / (3 / 16) - 2), harmanTwoPrimeKernel (3 / 16) β ≤ 5868031 / 12500000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (3 / 16)) (Set.Icc 1 ((3 / 4 + 1 / 1000000) / (3 / 16) - 2)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ (3 / 4 + 1 / 1000000) / (3 / 16) - 2 →
      IntervalIntegrable (harmanTwoPrimeKernel (3 / 16)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (9 / 5) (19 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (19 / 10) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (19 / 10) (2) (by norm_num) (by norm_num) (by norm_num))
      (ii (2) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_1_b_0, harmanTwoPrimeKernel_cell_1_b_1, harmanTwoPrimeKernel_cell_1_b_2, harmanTwoPrimeKernel_cell_1_b_3, harmanTwoPrimeKernel_cell_1_b_4, harmanTwoPrimeKernel_cell_1_b_5, harmanTwoPrimeKernel_cell_1_b_6, harmanTwoPrimeKernel_cell_1_b_7, harmanTwoPrimeKernel_cell_1_b_8, harmanTwoPrimeKernel_cell_1_b_9, harmanTwoPrimeKernel_cell_1_b_10]

theorem harmanDiscardTwoPrimeSection_le_strip_1 :
    ∀ x ∈ Set.Icc (65 / 352 : ℝ) (3 / 16), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (65 / 352) (3 / 16) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (3 / 4 + 1 / 1000000) (56746977 / 125000000) (5868031 / 12500000)
        (logUpper 1 ((3 / 4 + 1 / 1000000) / (3 / 16) - 2 + (3 / 4 + 1 / 1000000) * (1 / (65 / 352) - 1 / (3 / 16)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_one (by norm_num) (by norm_num) (by norm_num))
    (log_le_logUpper 1 (by norm_num)) harmanTwoPrimeKernel_integral_1_a
    harmanTwoPrimeKernel_integral_1_b

theorem harmanTwoPrimeStripEnvelope_integral_1 :
    ∫ x in (65 / 352 : ℝ)..(3 / 16),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (65 / 352) (3 / 16) ((3 / 4 + 1 / 1000000) / (3 / 16) - 2) (3 / 4 + 1 / 1000000) (56746977 / 125000000) (5868031 / 12500000)
        (logUpper 1 ((3 / 4 + 1 / 1000000) / (3 / 16) - 2 + (3 / 4 + 1 / 1000000) * (1 / (65 / 352) - 1 / (3 / 16)))) x / x ≤ 7525861 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 2779809 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 7946371 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 25414143 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 8594353 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (3 / 16) β ≤ 42996169 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 6432527 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 59948371 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (3 / 16) β ≤ 536249 / 7812500 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_8 :
    ∫ β in (9 / 5 : ℝ)..(19 / 10), harmanTwoPrimeKernel (3 / 16) β ≤ 77725939 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 9 / 5)
      (c₂ := 19 / 10) (m := 37 / 20) (U := logUpper 0 (37 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_9 :
    ∫ β in (19 / 10 : ℝ)..(2), harmanTwoPrimeKernel (3 / 16) β ≤ 21855767 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 19 / 10)
      (c₂ := 2) (m := 39 / 20) (U := logUpper 0 (39 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_a_10 :
    ∫ β in (2 : ℝ)..((2 + 1 / 1000000 / (999999 / 5000000))), harmanTwoPrimeKernel (3 / 16) β ≤ 4621 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 3 / 16) (c₁ := 2)
      (c₂ := (2 + 1 / 1000000 / (999999 / 5000000))) (m := 4000001 / 1999998) (U := logUpper 1 (4000001 / 1999998))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 1 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_2_a :
    ∫ β in (1 : ℝ)..(2 + 1 / 1000000 / (999999 / 5000000)), harmanTwoPrimeKernel (3 / 16) β ≤ 469442171 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (3 / 16)) (Set.Icc 1 (2 + 1 / 1000000 / (999999 / 5000000))) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 2 + 1 / 1000000 / (999999 / 5000000) →
      IntervalIntegrable (harmanTwoPrimeKernel (3 / 16)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (9 / 5) (19 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (19 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (19 / 10) (2) (by norm_num) (by norm_num) (by norm_num))
      (ii (2) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_2_a_0, harmanTwoPrimeKernel_cell_2_a_1, harmanTwoPrimeKernel_cell_2_a_2, harmanTwoPrimeKernel_cell_2_a_3, harmanTwoPrimeKernel_cell_2_a_4, harmanTwoPrimeKernel_cell_2_a_5, harmanTwoPrimeKernel_cell_2_a_6, harmanTwoPrimeKernel_cell_2_a_7, harmanTwoPrimeKernel_cell_2_a_8, harmanTwoPrimeKernel_cell_2_a_9, harmanTwoPrimeKernel_cell_2_a_10]

theorem harmanTwoPrimeKernel_cell_2_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 3055719 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 1759459 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 28377557 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 387573 / 10000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 49000593 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 11873039 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 70119831 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 40783169 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_8 :
    ∫ β in (9 / 5 : ℝ)..(19 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 94068029 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 9 / 5)
      (c₂ := 19 / 10) (m := 37 / 20) (U := logUpper 0 (37 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_9 :
    ∫ β in (19 / 10 : ℝ)..(2), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 10809037 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 19 / 10)
      (c₂ := 2) (m := 39 / 20) (U := logUpper 0 (39 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_2_b_10 :
    ∫ β in (2 : ℝ)..((2 + 1 / 1000000 / (999999 / 5000000))), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 5777 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 2)
      (c₂ := (2 + 1 / 1000000 / (999999 / 5000000))) (m := 4000001 / 1999998) (U := logUpper 1 (4000001 / 1999998))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 1 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_2_b :
    ∫ β in (1 : ℝ)..(2 + 1 / 1000000 / (999999 / 5000000)), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 276528509 / 500000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (999999 / 5000000)) (Set.Icc 1 (2 + 1 / 1000000 / (999999 / 5000000))) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 2 + 1 / 1000000 / (999999 / 5000000) →
      IntervalIntegrable (harmanTwoPrimeKernel (999999 / 5000000)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (9 / 5) (19 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (19 / 10) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (19 / 10) (2) (by norm_num) (by norm_num) (by norm_num))
      (ii (2) (2 + 1 / 1000000 / (999999 / 5000000)) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_2_b_0, harmanTwoPrimeKernel_cell_2_b_1, harmanTwoPrimeKernel_cell_2_b_2, harmanTwoPrimeKernel_cell_2_b_3, harmanTwoPrimeKernel_cell_2_b_4, harmanTwoPrimeKernel_cell_2_b_5, harmanTwoPrimeKernel_cell_2_b_6, harmanTwoPrimeKernel_cell_2_b_7, harmanTwoPrimeKernel_cell_2_b_8, harmanTwoPrimeKernel_cell_2_b_9, harmanTwoPrimeKernel_cell_2_b_10]

theorem harmanDiscardTwoPrimeSection_le_strip_2 :
    ∀ x ∈ Set.Icc (3 / 16 : ℝ) (999999 / 5000000), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (3 / 16) (999999 / 5000000) (2 + 1 / 1000000 / (999999 / 5000000)) (1 / 1000000) (469442171 / 1000000000) (276528509 / 500000000)
        (logUpper 1 (2 + 1 / 1000000 / (999999 / 5000000) + (1 / 1000000) * (1 / (3 / 16) - 1 / (999999 / 5000000)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_two (by norm_num) (by norm_num) (by norm_num))
    (log_le_logUpper 1 (by norm_num)) harmanTwoPrimeKernel_integral_2_a
    harmanTwoPrimeKernel_integral_2_b

theorem harmanTwoPrimeStripEnvelope_integral_2 :
    ∫ x in (3 / 16 : ℝ)..(999999 / 5000000),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (3 / 16) (999999 / 5000000) (2 + 1 / 1000000 / (999999 / 5000000)) (1 / 1000000) (469442171 / 1000000000) (276528509 / 500000000)
        (logUpper 1 (2 + 1 / 1000000 / (999999 / 5000000) + (1 / 1000000) * (1 / (3 / 16) - 1 / (999999 / 5000000)))) x / x ≤ 32990609 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 3055719 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 1759459 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 28377557 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 387573 / 10000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 49000593 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 11873039 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 70119831 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 40783169 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_a_8 :
    ∫ β in (9 / 5 : ℝ)..((1 / (41 / 200) - 3)), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 36116349 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 999999 / 5000000) (c₁ := 9 / 5)
      (c₂ := (1 / (41 / 200) - 3)) (m := 377 / 205) (U := logUpper 0 (377 / 205))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_3_a :
    ∫ β in (1 : ℝ)..(1 / (41 / 200) - 3), harmanTwoPrimeKernel (999999 / 5000000) β ≤ 21156277 / 50000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (999999 / 5000000)) (Set.Icc 1 (1 / (41 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (41 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (999999 / 5000000)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_3_a_0, harmanTwoPrimeKernel_cell_3_a_1, harmanTwoPrimeKernel_cell_3_a_2, harmanTwoPrimeKernel_cell_3_a_3, harmanTwoPrimeKernel_cell_3_a_4, harmanTwoPrimeKernel_cell_3_a_5, harmanTwoPrimeKernel_cell_3_a_6, harmanTwoPrimeKernel_cell_3_a_7, harmanTwoPrimeKernel_cell_3_a_8]

theorem harmanTwoPrimeKernel_cell_3_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (41 / 200) β ≤ 6364173 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 3676441 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (41 / 200) β ≤ 5953281 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 40839393 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (41 / 200) β ≤ 6487637 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 63253877 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (41 / 200) β ≤ 75228583 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_7 :
    ∫ β in (17 / 10 : ℝ)..(9 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 11027061 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 17 / 10)
      (c₂ := 9 / 5) (m := 7 / 4) (U := logUpper 0 (7 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_3_b_8 :
    ∫ β in (9 / 5 : ℝ)..((1 / (41 / 200) - 3)), harmanTwoPrimeKernel (41 / 200) β ≤ 78766747 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 9 / 5)
      (c₂ := (1 / (41 / 200) - 3)) (m := 377 / 205) (U := logUpper 0 (377 / 205))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_3_b :
    ∫ β in (1 : ℝ)..(1 / (41 / 200) - 3), harmanTwoPrimeKernel (41 / 200) β ≤ 452718967 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (41 / 200)) (Set.Icc 1 (1 / (41 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (41 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (41 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (17 / 10) (9 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (9 / 5) (1 / (41 / 200) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_3_b_0, harmanTwoPrimeKernel_cell_3_b_1, harmanTwoPrimeKernel_cell_3_b_2, harmanTwoPrimeKernel_cell_3_b_3, harmanTwoPrimeKernel_cell_3_b_4, harmanTwoPrimeKernel_cell_3_b_5, harmanTwoPrimeKernel_cell_3_b_6, harmanTwoPrimeKernel_cell_3_b_7, harmanTwoPrimeKernel_cell_3_b_8]

theorem harmanDiscardTwoPrimeSection_le_strip_3 :
    ∀ x ∈ Set.Icc (999999 / 5000000 : ℝ) (41 / 200), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (999999 / 5000000) (41 / 200) (1 / (41 / 200) - 3) (1) (21156277 / 50000000) (452718967 / 1000000000)
        (logUpper 1 (1 / (41 / 200) - 3 + (1) * (1 / (999999 / 5000000) - 1 / (41 / 200)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 1 (by norm_num)) harmanTwoPrimeKernel_integral_3_a
    harmanTwoPrimeKernel_integral_3_b

theorem harmanTwoPrimeStripEnvelope_integral_3 :
    ∫ x in (999999 / 5000000 : ℝ)..(41 / 200),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (999999 / 5000000) (41 / 200) (1 / (41 / 200) - 3) (1) (21156277 / 50000000) (452718967 / 1000000000)
        (logUpper 1 (1 / (41 / 200) - 3 + (1) * (1 / (999999 / 5000000) - 1 / (41 / 200)))) x / x ≤ 12837449 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

end

end RHTower.Sieve
