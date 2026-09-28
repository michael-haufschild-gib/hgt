import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardTwoPrimeStripBounds

/-!
# Two-prime-cofactor section: strip bounds for `0.205 ≤ α₂ ≤ 1/4`

For each strip `[a, b]` of the `α₂`-range, the kernel integrals `∫₁^{B} log β/((1+β)(1-(2+β)c)) dβ`
at `c = a, b` are bounded on `β`-cells of width `1/10` by the tangent of `log` and the chords of
the two reciprocals; the section is then below the affine strip envelope, whose integral against
`dα₂/α₂` is bounded through the chord of `1/α₂`.  Parameter `κ = 10⁻⁶`.
-/

namespace RHTower.Sieve

open Real intervalIntegral

noncomputable section

theorem harmanTwoPrimeKernel_cell_4_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (41 / 200) β ≤ 6364173 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 3676441 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (41 / 200) β ≤ 5953281 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 40839393 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (41 / 200) β ≤ 6487637 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (41 / 200) β ≤ 63253877 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (41 / 200) β ≤ 75228583 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_a_7 :
    ∫ β in (17 / 10 : ℝ)..((1 / (21 / 100) - 3)), harmanTwoPrimeKernel (41 / 200) β ≤ 52938357 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 41 / 200) (c₁ := 17 / 10)
      (c₂ := (1 / (21 / 100) - 3)) (m := 727 / 420) (U := logUpper 0 (727 / 420))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_4_a :
    ∫ β in (1 : ℝ)..(1 / (21 / 100) - 3), harmanTwoPrimeKernel (41 / 200) β ≤ 338674089 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (41 / 200)) (Set.Icc 1 (1 / (21 / 100) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (21 / 100) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (41 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_4_a_0, harmanTwoPrimeKernel_cell_4_a_1, harmanTwoPrimeKernel_cell_4_a_2, harmanTwoPrimeKernel_cell_4_a_3, harmanTwoPrimeKernel_cell_4_a_4, harmanTwoPrimeKernel_cell_4_a_5, harmanTwoPrimeKernel_cell_4_a_6, harmanTwoPrimeKernel_cell_4_a_7]

theorem harmanTwoPrimeKernel_cell_4_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (21 / 100) β ≤ 6638741 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (21 / 100) β ≤ 19243761 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (21 / 100) β ≤ 31298459 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (21 / 100) β ≤ 8631677 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (21 / 100) β ≤ 55167447 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (21 / 100) β ≤ 33844593 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_6 :
    ∫ β in (8 / 5 : ℝ)..(17 / 10), harmanTwoPrimeKernel (21 / 100) β ≤ 81142737 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 8 / 5)
      (c₂ := 17 / 10) (m := 33 / 20) (U := logUpper 0 (33 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_4_b_7 :
    ∫ β in (17 / 10 : ℝ)..((1 / (21 / 100) - 3)), harmanTwoPrimeKernel (21 / 100) β ≤ 14377753 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 17 / 10)
      (c₂ := (1 / (21 / 100) - 3)) (m := 727 / 420) (U := logUpper 0 (727 / 420))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_4_b :
    ∫ β in (1 : ℝ)..(1 / (21 / 100) - 3), harmanTwoPrimeKernel (21 / 100) β ≤ 2826951 / 7812500 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (21 / 100)) (Set.Icc 1 (1 / (21 / 100) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (21 / 100) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (21 / 100)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (8 / 5) (17 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (17 / 10) (1 / (21 / 100) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_4_b_0, harmanTwoPrimeKernel_cell_4_b_1, harmanTwoPrimeKernel_cell_4_b_2, harmanTwoPrimeKernel_cell_4_b_3, harmanTwoPrimeKernel_cell_4_b_4, harmanTwoPrimeKernel_cell_4_b_5, harmanTwoPrimeKernel_cell_4_b_6, harmanTwoPrimeKernel_cell_4_b_7]

theorem harmanDiscardTwoPrimeSection_le_strip_4 :
    ∀ x ∈ Set.Icc (41 / 200 : ℝ) (21 / 100), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (41 / 200) (21 / 100) (1 / (21 / 100) - 3) (1) (338674089 / 1000000000) (2826951 / 7812500)
        (logUpper 0 (1 / (21 / 100) - 3 + (1) * (1 / (41 / 200) - 1 / (21 / 100)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_4_a
    harmanTwoPrimeKernel_integral_4_b

theorem harmanTwoPrimeStripEnvelope_integral_4 :
    ∫ x in (41 / 200 : ℝ)..(21 / 100),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (41 / 200) (21 / 100) (1 / (21 / 100) - 3) (1) (338674089 / 1000000000) (2826951 / 7812500)
        (logUpper 0 (1 / (21 / 100) - 3 + (1) * (1 / (41 / 200) - 1 / (21 / 100)))) x / x ≤ 10168359 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (21 / 100) β ≤ 6638741 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (21 / 100) β ≤ 19243761 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (21 / 100) β ≤ 31298459 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (21 / 100) β ≤ 8631677 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (21 / 100) β ≤ 55167447 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (21 / 100) β ≤ 33844593 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_a_6 :
    ∫ β in (8 / 5 : ℝ)..((1 / (43 / 200) - 3)), harmanTwoPrimeKernel (21 / 100) β ≤ 39702067 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 21 / 100) (c₁ := 8 / 5)
      (c₂ := (1 / (43 / 200) - 3)) (m := 699 / 430) (U := logUpper 0 (699 / 430))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_5_a :
    ∫ β in (1 : ℝ)..(1 / (43 / 200) - 3), harmanTwoPrimeKernel (21 / 100) β ≤ 131449023 / 500000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (21 / 100)) (Set.Icc 1 (1 / (43 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (43 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (21 / 100)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_5_a_0, harmanTwoPrimeKernel_cell_5_a_1, harmanTwoPrimeKernel_cell_5_a_2, harmanTwoPrimeKernel_cell_5_a_3, harmanTwoPrimeKernel_cell_5_a_4, harmanTwoPrimeKernel_cell_5_a_5, harmanTwoPrimeKernel_cell_5_a_6]

theorem harmanTwoPrimeKernel_cell_5_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (43 / 200) β ≤ 1734529 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (43 / 200) β ≤ 2523781 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (43 / 200) β ≤ 16498603 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (43 / 200) β ≤ 45757377 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (43 / 200) β ≤ 29436953 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_b_5 :
    ∫ β in (3 / 2 : ℝ)..(8 / 5), harmanTwoPrimeKernel (43 / 200) β ≤ 72795741 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 3 / 2)
      (c₂ := 8 / 5) (m := 31 / 20) (U := logUpper 0 (31 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_5_b_6 :
    ∫ β in (8 / 5 : ℝ)..((1 / (43 / 200) - 3)), harmanTwoPrimeKernel (43 / 200) β ≤ 4297183 / 100000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 8 / 5)
      (c₂ := (1 / (43 / 200) - 3)) (m := 699 / 430) (U := logUpper 0 (699 / 430))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_5_b :
    ∫ β in (1 : ℝ)..(1 / (43 / 200) - 3), harmanTwoPrimeKernel (43 / 200) β ≤ 35065553 / 125000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (43 / 200)) (Set.Icc 1 (1 / (43 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (43 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (43 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (3 / 2) (8 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (8 / 5) (1 / (43 / 200) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_5_b_0, harmanTwoPrimeKernel_cell_5_b_1, harmanTwoPrimeKernel_cell_5_b_2, harmanTwoPrimeKernel_cell_5_b_3, harmanTwoPrimeKernel_cell_5_b_4, harmanTwoPrimeKernel_cell_5_b_5, harmanTwoPrimeKernel_cell_5_b_6]

theorem harmanDiscardTwoPrimeSection_le_strip_5 :
    ∀ x ∈ Set.Icc (21 / 100 : ℝ) (43 / 200), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (21 / 100) (43 / 200) (1 / (43 / 200) - 3) (1) (131449023 / 500000000) (35065553 / 125000000)
        (logUpper 0 (1 / (43 / 200) - 3 + (1) * (1 / (21 / 100) - 1 / (43 / 200)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_5_a
    harmanTwoPrimeKernel_integral_5_b

theorem harmanTwoPrimeStripEnvelope_integral_5 :
    ∫ x in (21 / 100 : ℝ)..(43 / 200),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (21 / 100) (43 / 200) (1 / (43 / 200) - 3) (1) (131449023 / 500000000) (35065553 / 125000000)
        (logUpper 0 (1 / (43 / 200) - 3 + (1) * (1 / (21 / 100) - 1 / (43 / 200)))) x / x ≤ 1963931 / 250000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (43 / 200) β ≤ 1734529 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (43 / 200) β ≤ 2523781 / 125000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (43 / 200) β ≤ 16498603 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (43 / 200) β ≤ 45757377 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_a_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (43 / 200) β ≤ 29436953 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_a_5 :
    ∫ β in (3 / 2 : ℝ)..((1 / (11 / 50) - 3)), harmanTwoPrimeKernel (43 / 200) β ≤ 31246637 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 43 / 200) (c₁ := 3 / 2)
      (c₂ := (1 / (11 / 50) - 3)) (m := 67 / 44) (U := logUpper 0 (67 / 44))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_6_a :
    ∫ β in (1 : ℝ)..(1 / (11 / 50) - 3), harmanTwoPrimeKernel (43 / 200) β ≤ 19600349 / 100000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (43 / 200)) (Set.Icc 1 (1 / (11 / 50) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (11 / 50) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (43 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_6_a_0, harmanTwoPrimeKernel_cell_6_a_1, harmanTwoPrimeKernel_cell_6_a_2, harmanTwoPrimeKernel_cell_6_a_3, harmanTwoPrimeKernel_cell_6_a_4, harmanTwoPrimeKernel_cell_6_a_5]

theorem harmanTwoPrimeKernel_cell_6_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (11 / 50) β ≤ 7265827 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (11 / 50) β ≤ 21234909 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (11 / 50) β ≤ 6978299 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (11 / 50) β ≤ 12172627 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_b_4 :
    ∫ β in (7 / 5 : ℝ)..(3 / 2), harmanTwoPrimeKernel (11 / 50) β ≤ 31558093 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 7 / 5)
      (c₂ := 3 / 2) (m := 29 / 20) (U := logUpper 0 (29 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_6_b_5 :
    ∫ β in (3 / 2 : ℝ)..((1 / (11 / 50) - 3)), harmanTwoPrimeKernel (11 / 50) β ≤ 2106019 / 62500000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 3 / 2)
      (c₂ := (1 / (11 / 50) - 3)) (m := 67 / 44) (U := logUpper 0 (67 / 44))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_6_b :
    ∫ β in (1 : ℝ)..(1 / (11 / 50) - 3), harmanTwoPrimeKernel (11 / 50) β ≤ 208895229 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (11 / 50)) (Set.Icc 1 (1 / (11 / 50) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (11 / 50) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (11 / 50)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (7 / 5) (3 / 2) (by norm_num) (by norm_num) (by norm_num))
      (ii (3 / 2) (1 / (11 / 50) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_6_b_0, harmanTwoPrimeKernel_cell_6_b_1, harmanTwoPrimeKernel_cell_6_b_2, harmanTwoPrimeKernel_cell_6_b_3, harmanTwoPrimeKernel_cell_6_b_4, harmanTwoPrimeKernel_cell_6_b_5]

theorem harmanDiscardTwoPrimeSection_le_strip_6 :
    ∀ x ∈ Set.Icc (43 / 200 : ℝ) (11 / 50), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (43 / 200) (11 / 50) (1 / (11 / 50) - 3) (1) (19600349 / 100000000) (208895229 / 1000000000)
        (logUpper 0 (1 / (11 / 50) - 3 + (1) * (1 / (43 / 200) - 1 / (11 / 50)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_6_a
    harmanTwoPrimeKernel_integral_6_b

theorem harmanTwoPrimeStripEnvelope_integral_6 :
    ∫ x in (43 / 200 : ℝ)..(11 / 50),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (43 / 200) (11 / 50) (1 / (11 / 50) - 3) (1) (19600349 / 100000000) (208895229 / 1000000000)
        (logUpper 0 (1 / (11 / 50) - 3 + (1) * (1 / (43 / 200) - 1 / (11 / 50)))) x / x ≤ 5876247 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (11 / 50) β ≤ 7265827 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (11 / 50) β ≤ 21234909 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (11 / 50) β ≤ 6978299 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_a_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (11 / 50) β ≤ 12172627 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_a_4 :
    ∫ β in (7 / 5 : ℝ)..((1 / (9 / 40) - 3)), harmanTwoPrimeKernel (11 / 50) β ≤ 13084117 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 11 / 50) (c₁ := 7 / 5)
      (c₂ := (1 / (9 / 40) - 3)) (m := 64 / 45) (U := logUpper 0 (64 / 45))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_7_a :
    ∫ β in (1 : ℝ)..(1 / (9 / 40) - 3), harmanTwoPrimeKernel (11 / 50) β ≤ 138250973 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (11 / 50)) (Set.Icc 1 (1 / (9 / 40) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (9 / 40) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (11 / 50)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_7_a_0, harmanTwoPrimeKernel_cell_7_a_1, harmanTwoPrimeKernel_cell_7_a_2, harmanTwoPrimeKernel_cell_7_a_3, harmanTwoPrimeKernel_cell_7_a_4]

theorem harmanTwoPrimeKernel_cell_7_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (9 / 40) β ≤ 1525221 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (9 / 40) β ≤ 22393901 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (9 / 40) β ≤ 18508633 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_b_3 :
    ∫ β in (13 / 10 : ℝ)..(7 / 5), harmanTwoPrimeKernel (9 / 40) β ≤ 52026887 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 13 / 10)
      (c₂ := 7 / 5) (m := 27 / 20) (U := logUpper 0 (27 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_7_b_4 :
    ∫ β in (7 / 5 : ℝ)..((1 / (9 / 40) - 3)), harmanTwoPrimeKernel (9 / 40) β ≤ 28117977 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 7 / 5)
      (c₂ := (1 / (9 / 40) - 3)) (m := 64 / 45) (U := logUpper 0 (64 / 45))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_7_b :
    ∫ β in (1 : ℝ)..(1 / (9 / 40) - 3), harmanTwoPrimeKernel (9 / 40) β ≤ 18397767 / 125000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (9 / 40)) (Set.Icc 1 (1 / (9 / 40) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (9 / 40) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (9 / 40)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (13 / 10) (7 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (7 / 5) (1 / (9 / 40) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_7_b_0, harmanTwoPrimeKernel_cell_7_b_1, harmanTwoPrimeKernel_cell_7_b_2, harmanTwoPrimeKernel_cell_7_b_3, harmanTwoPrimeKernel_cell_7_b_4]

theorem harmanDiscardTwoPrimeSection_le_strip_7 :
    ∀ x ∈ Set.Icc (11 / 50 : ℝ) (9 / 40), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (11 / 50) (9 / 40) (1 / (9 / 40) - 3) (1) (138250973 / 1000000000) (18397767 / 125000000)
        (logUpper 0 (1 / (9 / 40) - 3 + (1) * (1 / (11 / 50) - 1 / (9 / 40)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_7_a
    harmanTwoPrimeKernel_integral_7_b

theorem harmanTwoPrimeStripEnvelope_integral_7 :
    ∫ x in (11 / 50 : ℝ)..(9 / 40),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (11 / 50) (9 / 40) (1 / (9 / 40) - 3) (1) (138250973 / 1000000000) (18397767 / 125000000)
        (logUpper 0 (1 / (9 / 40) - 3 + (1) * (1 / (11 / 50) - 1 / (9 / 40)))) x / x ≤ 4210913 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (9 / 40) β ≤ 1525221 / 200000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (9 / 40) β ≤ 22393901 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_a_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (9 / 40) β ≤ 18508633 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_a_3 :
    ∫ β in (13 / 10 : ℝ)..((1 / (23 / 100) - 3)), harmanTwoPrimeKernel (9 / 40) β ≤ 22920727 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 9 / 40) (c₁ := 13 / 10)
      (c₂ := (1 / (23 / 100) - 3)) (m := 609 / 460) (U := logUpper 0 (609 / 460))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_8_a :
    ∫ β in (1 : ℝ)..(1 / (23 / 100) - 3), harmanTwoPrimeKernel (9 / 40) β ≤ 89957999 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (9 / 40)) (Set.Icc 1 (1 / (23 / 100) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (23 / 100) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (9 / 40)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (23 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (23 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (23 / 100) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_8_a_0, harmanTwoPrimeKernel_cell_8_a_1, harmanTwoPrimeKernel_cell_8_a_2, harmanTwoPrimeKernel_cell_8_a_3]

theorem harmanTwoPrimeKernel_cell_8_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (23 / 100) β ≤ 8024073 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (23 / 100) β ≤ 23687141 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_b_2 :
    ∫ β in (6 / 5 : ℝ)..(13 / 10), harmanTwoPrimeKernel (23 / 100) β ≤ 39419873 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 6 / 5)
      (c₂ := 13 / 10) (m := 5 / 4) (U := logUpper 0 (5 / 4))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_8_b_3 :
    ∫ β in (13 / 10 : ℝ)..((1 / (23 / 100) - 3)), harmanTwoPrimeKernel (23 / 100) β ≤ 196331 / 8000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 13 / 10)
      (c₂ := (1 / (23 / 100) - 3)) (m := 609 / 460) (U := logUpper 0 (609 / 460))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_8_b :
    ∫ β in (1 : ℝ)..(1 / (23 / 100) - 3), harmanTwoPrimeKernel (23 / 100) β ≤ 47836231 / 500000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (23 / 100)) (Set.Icc 1 (1 / (23 / 100) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (23 / 100) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (23 / 100)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (23 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (23 / 100) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (6 / 5) (13 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (13 / 10) (1 / (23 / 100) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_8_b_0, harmanTwoPrimeKernel_cell_8_b_1, harmanTwoPrimeKernel_cell_8_b_2, harmanTwoPrimeKernel_cell_8_b_3]

theorem harmanDiscardTwoPrimeSection_le_strip_8 :
    ∀ x ∈ Set.Icc (9 / 40 : ℝ) (23 / 100), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (9 / 40) (23 / 100) (1 / (23 / 100) - 3) (1) (89957999 / 1000000000) (47836231 / 500000000)
        (logUpper 0 (1 / (23 / 100) - 3 + (1) * (1 / (9 / 40) - 1 / (23 / 100)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_8_a
    harmanTwoPrimeKernel_integral_8_b

theorem harmanTwoPrimeStripEnvelope_integral_8 :
    ∫ x in (9 / 40 : ℝ)..(23 / 100),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (9 / 40) (23 / 100) (1 / (23 / 100) - 3) (1) (89957999 / 1000000000) (47836231 / 500000000)
        (logUpper 0 (1 / (23 / 100) - 3 + (1) * (1 / (9 / 40) - 1 / (23 / 100)))) x / x ≤ 2843943 / 1000000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_9_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (23 / 100) β ≤ 8024073 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_9_a_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (23 / 100) β ≤ 23687141 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_9_a_2 :
    ∫ β in (6 / 5 : ℝ)..((1 / (47 / 200) - 3)), harmanTwoPrimeKernel (23 / 100) β ≤ 9895889 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 23 / 100) (c₁ := 6 / 5)
      (c₂ := (1 / (47 / 200) - 3)) (m := 577 / 470) (U := logUpper 0 (577 / 470))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_9_a :
    ∫ β in (1 : ℝ)..(1 / (47 / 200) - 3), harmanTwoPrimeKernel (23 / 100) β ≤ 3218937 / 62500000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (23 / 100)) (Set.Icc 1 (1 / (47 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (47 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (23 / 100)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (47 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (47 / 200) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_9_a_0, harmanTwoPrimeKernel_cell_9_a_1, harmanTwoPrimeKernel_cell_9_a_2]

theorem harmanTwoPrimeKernel_cell_9_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (47 / 200) β ≤ 8465987 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 47 / 200) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_9_b_1 :
    ∫ β in (11 / 10 : ℝ)..(6 / 5), harmanTwoPrimeKernel (47 / 200) β ≤ 6284869 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 47 / 200) (c₁ := 11 / 10)
      (c₂ := 6 / 5) (m := 23 / 20) (U := logUpper 0 (23 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_9_b_2 :
    ∫ β in (6 / 5 : ℝ)..((1 / (47 / 200) - 3)), harmanTwoPrimeKernel (47 / 200) β ≤ 5279579 / 250000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 47 / 200) (c₁ := 6 / 5)
      (c₂ := (1 / (47 / 200) - 3)) (m := 577 / 470) (U := logUpper 0 (577 / 470))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_9_b :
    ∫ β in (1 : ℝ)..(1 / (47 / 200) - 3), harmanTwoPrimeKernel (47 / 200) β ≤ 54723779 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (47 / 200)) (Set.Icc 1 (1 / (47 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (47 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (47 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (47 / 200) - 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (ii (11 / 10) (6 / 5) (by norm_num) (by norm_num) (by norm_num))
      (ii (6 / 5) (1 / (47 / 200) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_9_b_0, harmanTwoPrimeKernel_cell_9_b_1, harmanTwoPrimeKernel_cell_9_b_2]

theorem harmanDiscardTwoPrimeSection_le_strip_9 :
    ∀ x ∈ Set.Icc (23 / 100 : ℝ) (47 / 200), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (23 / 100) (47 / 200) (1 / (47 / 200) - 3) (1) (3218937 / 62500000) (54723779 / 1000000000)
        (logUpper 0 (1 / (47 / 200) - 3 + (1) * (1 / (23 / 100) - 1 / (47 / 200)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_9_a
    harmanTwoPrimeKernel_integral_9_b

theorem harmanTwoPrimeStripEnvelope_integral_9 :
    ∫ x in (23 / 100 : ℝ)..(47 / 200),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (23 / 100) (47 / 200) (1 / (47 / 200) - 3) (1) (3218937 / 62500000) (54723779 / 1000000000)
        (logUpper 0 (1 / (47 / 200) - 3 + (1) * (1 / (23 / 100) - 1 / (47 / 200)))) x / x ≤ 440619 / 250000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_10_a_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (47 / 200) β ≤ 8465987 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 47 / 200) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_10_a_1 :
    ∫ β in (11 / 10 : ℝ)..((1 / (6 / 25) - 3)), harmanTwoPrimeKernel (47 / 200) β ≤ 743263 / 50000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 47 / 200) (c₁ := 11 / 10)
      (c₂ := (1 / (6 / 25) - 3)) (m := 17 / 15) (U := logUpper 0 (17 / 15))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_10_a :
    ∫ β in (1 : ℝ)..(1 / (6 / 25) - 3), harmanTwoPrimeKernel (47 / 200) β ≤ 23331247 / 1000000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (47 / 200)) (Set.Icc 1 (1 / (6 / 25) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (6 / 25) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (47 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (6 / 25) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_10_a_0, harmanTwoPrimeKernel_cell_10_a_1]

theorem harmanTwoPrimeKernel_cell_10_b_0 :
    ∫ β in (1 : ℝ)..(11 / 10), harmanTwoPrimeKernel (6 / 25) β ≤ 358383 / 40000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 6 / 25) (c₁ := 1)
      (c₂ := 11 / 10) (m := 21 / 20) (U := logUpper 0 (21 / 20))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_10_b_1 :
    ∫ β in (11 / 10 : ℝ)..((1 / (6 / 25) - 3)), harmanTwoPrimeKernel (6 / 25) β ≤ 15809771 / 1000000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 6 / 25) (c₁ := 11 / 10)
      (c₂ := (1 / (6 / 25) - 3)) (m := 17 / 15) (U := logUpper 0 (17 / 15))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_10_b :
    ∫ β in (1 : ℝ)..(1 / (6 / 25) - 3), harmanTwoPrimeKernel (6 / 25) β ≤ 12384673 / 500000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (6 / 25)) (Set.Icc 1 (1 / (6 / 25) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (6 / 25) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (6 / 25)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (ii (1) (11 / 10) (by norm_num) (by norm_num) (by norm_num))
      (ii (11 / 10) (1 / (6 / 25) - 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [harmanTwoPrimeKernel_cell_10_b_0, harmanTwoPrimeKernel_cell_10_b_1]

theorem harmanDiscardTwoPrimeSection_le_strip_10 :
    ∀ x ∈ Set.Icc (47 / 200 : ℝ) (6 / 25), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (47 / 200) (6 / 25) (1 / (6 / 25) - 3) (1) (23331247 / 1000000000) (12384673 / 500000000)
        (logUpper 0 (1 / (6 / 25) - 3 + (1) * (1 / (47 / 200) - 1 / (6 / 25)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_10_a
    harmanTwoPrimeKernel_integral_10_b

theorem harmanTwoPrimeStripEnvelope_integral_10 :
    ∫ x in (47 / 200 : ℝ)..(6 / 25),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (47 / 200) (6 / 25) (1 / (6 / 25) - 3) (1) (23331247 / 1000000000) (12384673 / 500000000)
        (logUpper 0 (1 / (6 / 25) - 3 + (1) * (1 / (47 / 200) - 1 / (6 / 25)))) x / x ≤ 119543 / 125000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_cell_11_a_0 :
    ∫ β in (1 : ℝ)..((1 / (49 / 200) - 3)), harmanTwoPrimeKernel (6 / 25) β ≤ 74531 / 12500000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 6 / 25) (c₁ := 1)
      (c₂ := (1 / (49 / 200) - 3)) (m := 51 / 49) (U := logUpper 0 (51 / 49))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_11_a :
    ∫ β in (1 : ℝ)..(1 / (49 / 200) - 3), harmanTwoPrimeKernel (6 / 25) β ≤ 74531 / 12500000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (6 / 25)) (Set.Icc 1 (1 / (49 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (49 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (6 / 25)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  linarith [harmanTwoPrimeKernel_cell_11_a_0]

theorem harmanTwoPrimeKernel_cell_11_b_0 :
    ∫ β in (1 : ℝ)..((1 / (49 / 200) - 3)), harmanTwoPrimeKernel (49 / 200) β ≤ 3162681 / 500000000 :=
  (integral_harmanTwoPrimeKernel_cell_le (c := 49 / 200) (c₁ := 1)
      (c₂ := (1 / (49 / 200) - 3)) (m := 51 / 49) (U := logUpper 0 (51 / 49))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_logUpper 0 (by norm_num)) (by norm_num)).trans
    (by norm_num [harmanTwoPrimeCellBound, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_11_b :
    ∫ β in (1 : ℝ)..(1 / (49 / 200) - 3), harmanTwoPrimeKernel (49 / 200) β ≤ 3162681 / 500000000 := by
  have hc : ContinuousOn (harmanTwoPrimeKernel (49 / 200)) (Set.Icc 1 (1 / (49 / 200) - 3)) :=
    continuousOn_harmanTwoPrimeKernel one_pos (by norm_num) (by norm_num)
  have ii : ∀ x y : ℝ, 1 ≤ x → x ≤ y → y ≤ 1 / (49 / 200) - 3 →
      IntervalIntegrable (harmanTwoPrimeKernel (49 / 200)) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  linarith [harmanTwoPrimeKernel_cell_11_b_0]

theorem harmanDiscardTwoPrimeSection_le_strip_11 :
    ∀ x ∈ Set.Icc (6 / 25 : ℝ) (49 / 200), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (6 / 25) (49 / 200) (1 / (49 / 200) - 3) (1) (74531 / 12500000) (3162681 / 500000000)
        (logUpper 0 (1 / (49 / 200) - 3 + (1) * (1 / (6 / 25) - 1 / (49 / 200)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_11_a
    harmanTwoPrimeKernel_integral_11_b

theorem harmanTwoPrimeStripEnvelope_integral_11 :
    ∫ x in (6 / 25 : ℝ)..(49 / 200),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (6 / 25) (49 / 200) (1 / (49 / 200) - 3) (1) (74531 / 12500000) (3162681 / 500000000)
        (logUpper 0 (1 / (49 / 200) - 3 + (1) * (1 / (6 / 25) - 1 / (49 / 200)))) x / x ≤ 653 / 1562500 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

theorem harmanTwoPrimeKernel_integral_12_a :
    ∫ β in (1 : ℝ)..(1 / (1 / 4) - 3), harmanTwoPrimeKernel (49 / 200) β ≤ 0 := by
  rw [show (1 / (1 / 4) - 3 : ℝ) = 1 by norm_num, intervalIntegral.integral_same]

theorem harmanTwoPrimeKernel_integral_12_b :
    ∫ β in (1 : ℝ)..(1 / (1 / 4) - 3), harmanTwoPrimeKernel (1 / 4) β ≤ 0 := by
  rw [show (1 / (1 / 4) - 3 : ℝ) = 1 by norm_num, intervalIntegral.integral_same]

theorem harmanDiscardTwoPrimeSection_le_strip_12 :
    ∀ x ∈ Set.Icc (49 / 200 : ℝ) (1 / 4), harmanDiscardTwoPrimeSection (1 / 1000000) x ≤
      harmanTwoPrimeStripEnvelope (1 / 1000000) (49 / 200) (1 / 4) (1 / (1 / 4) - 3) (1) (0) (0)
        (logUpper 0 (1 / (1 / 4) - 3 + (1) * (1 / (49 / 200) - 1 / (1 / 4)))) x :=
  fun x hx => harmanDiscardTwoPrimeSection_le_wedge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num) (by norm_num)
    (harmanDiscardLow_wedge_self (by norm_num) (by norm_num))
    (log_le_logUpper 0 (by norm_num)) harmanTwoPrimeKernel_integral_12_a
    harmanTwoPrimeKernel_integral_12_b

theorem harmanTwoPrimeStripEnvelope_integral_12 :
    ∫ x in (49 / 200 : ℝ)..(1 / 4),
      harmanTwoPrimeStripEnvelope (1 / 1000000) (49 / 200) (1 / 4) (1 / (1 / 4) - 3) (1) (0) (0)
        (logUpper 0 (1 / (1 / 4) - 3 + (1) * (1 / (49 / 200) - 1 / (1 / 4)))) x / x ≤ 14201 / 100000000 :=
  (integral_harmanTwoPrimeStripEnvelope_div_le (by norm_num) (by norm_num)
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])).trans
    (by norm_num [harmanTwoPrimeStripEnvelope, logUpper, logSeriesUpper, logSeriesLower])

end

end RHTower.Sieve
