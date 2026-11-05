import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxDensity

/-!
# Typical logarithmic derivatives with a variable level

The exceptional-set estimate is uniform in the logarithmic-derivative level
`4 ≤ B ≤ log T`. Keeping this quantifier after the height threshold permits
levels much smaller than `sqrt (log T)` on fixed boxes right of the critical line.
-/

open Complex Set MeasureTheory Filter
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- One height threshold controls all levels `4 ≤ B ≤ log T` and all admitted boxes.
The four exceptional sets are zero shadows, two explicit-formula remainders,
and large values of the prime polynomial. -/
theorem exists_volume_not_zetaLogDerivScaleData_le_uniform_level :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ B : ℝ, 4 ≤ B → B ≤ Real.log T →
      ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → 30000 ≤ R * Real.log T →
        volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R B} ≤
          ENNReal.ofReal (C * T *
            (Real.log T / B * Real.exp (-(R * Real.log T / 120000)) +
              1 / (B ^ 2 * R ^ 2)) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨KE, hKE, hEFall⟩ := exists_selberg_explicit_formula_at_height
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hKE)
  obtain ⟨A, Kw, hA, _, hwin⟩ := exists_sum_selbergRightWindow_le
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_sum_mult_selbergMidZeros_le
  let C := 336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ +
    1600000 * Real.pi * C₀ + 1324800 / Real.pi + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  have hE2 := eventually_mul_log_add_pow_le_exp 40 1
    (show (0 : ℝ) < 1 / 30000 by norm_num)
  have hE5 := eventually_mul_log_add_pow_le_exp 2 (144 * Kw / Real.pi)
    (show (0 : ℝ) < 1 / 2 - 1 / 10000 by norm_num)
  have hE6 := eventually_mul_log_add_pow_le_exp 1 16
    (show (0 : ℝ) < 1 - 1 / 15000 by norm_num)
  filter_upwards [hwin, eventually_ge_atTop (max t₀ 64), hE2, hE5, hE6]
    with T hTwin hTt hE2 hE5 hE6
  intro B hB4 hBL R hR hR16 hκ
  have hT64 : 64 ≤ T := le_of_max_le_right hTt
  have hL0 : 0 < Real.log T := by linarith
  have hB0 : 0 < B := by linarith
  let ε := B / Real.log T
  have hε : 0 < ε := div_pos hB0 hL0
  have hε1 : ε ≤ 1 := (div_le_one hL0).mpr hBL
  have hεL : ε * Real.log T = B := div_mul_cancel₀ _ hL0.ne'
  let x := Real.exp (Real.log T / 30000)
  have hlx : Real.log x = Real.log T / 30000 := Real.log_exp _
  have hx : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
  have hRx : 1 ≤ 36 * R * Real.log x := by
    rw [hlx]
    nlinarith only [hκ]
  have hEF := selberg_explicit_formula_block hEFall ht₀ hT64
    (le_of_max_le_left hTt) hx
    (by dsimp only [x]; rw [show Real.log T / 30000 = 1 / 30000 * Real.log T by ring]
        simpa only [one_mul] using hE2)
    (by rw [hlx]; linarith)
  have hcL0 : 0 < 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 := by
    have := Real.log_pos hx
    positivity
  have hquarter : 0 < ε * Real.log T / 4 := by positivity
  have hfour : 4 ≤ ε * Real.log T := by rwa [hεL]
  have hbound := volume_not_zetaLogDerivScaleData_le_of
    (B := ε * Real.log T) (C₀ := C₀)
    (M_D := ε * Real.log T / 4)
    (M_L := ε * Real.log T / 4 /
      (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153))
    (M_F := ε * Real.log T / 4) hT64 hx hR hR16 hRx hEF
    (hC₀ T (by linarith)) hquarter (div_pos hquarter hcL0) hquarter
    (by rw [mul_div_cancel₀ _ hcL0.ne']; linarith only [hfour])
  have hterms := scale_terms_le hT64 rfl hR hR16 hκ hε hε1 hA hC₀pos
    (show x = Real.exp (Real.log T / 30000) from rfl) hE5 hE6
    (Finset.sum_nonneg fun w _ => by
      have := selbergRightWindow_pos (x := x) hR w
      positivity)
    (hTwin x R hx hR (by linarith) (by linarith) (by
      rw [hlx, show 6 * (Real.log T / 30000) / Real.log T = 1 / 5000 by
        field_simp; ring]
      norm_num))
  have h := hbound.trans hterms
  rw [hεL] at h
  have hscale : Real.exp (-(R * Real.log T / 120000)) / ε +
      1 / (ε ^ 2 * (R * Real.log T) ^ 2) =
      Real.log T / B * Real.exp (-(R * Real.log T / 120000)) +
        1 / (B ^ 2 * R ^ 2) := by
    dsimp only [ε]
    field_simp
  simpa only [hscale, C] using h

#print axioms exists_volume_not_zetaLogDerivScaleData_le_uniform_level

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
