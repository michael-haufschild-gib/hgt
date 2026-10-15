import GaloisForLFunctions.HTGeometry.LogNodeExponentialTail

/-!
# The pole of a function vanishing at the logarithms of the integers

Let `g` be continuous, compactly supported, `L`-Lipschitz, bounded by `C₀`, and let it vanish at
`log n` for every `n ≥ 2`.

**Theorem** (`abs_integral_mul_exp_half_le_of_log_blind`).  For every `N₀ ≥ 2`,
`|∫ g(y) e^{y/2} dy| ≤ 2C₀/√N₀ + √N₀ ∫_{−log N₀}^{log N₀} |g| + √2 L/√(N₀ − 1)`.

The three terms are the left tail (`e^{y/2} ≤ e^{−log N₀ /2}`), the window `|y| ≤ log N₀` and the
right tail beyond `log N₀`, where the zeros `log n` are `1/N₀`-dense and the Lipschitz bound makes
`g` small (`abs_intervalIntegral_mul_exp_half_le`).  Optimising `N₀` shows that a large exponential
moment of a blind function needs a large product of its Lipschitz constant and its mass near the
origin.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **Pole inequality for log-blind functions.** -/
theorem abs_integral_mul_exp_half_le_of_log_blind {g : ℝ → ℝ} {L C₀ R : ℝ} (hg : Continuous g)
    (hR0 : 0 ≤ R) (hR : ∀ y, R < |y| → g y = 0) (hL : 0 ≤ L)
    (hLip : ∀ y y', |g y - g y'| ≤ L * |y - y'|) (hC : ∀ y, |g y| ≤ C₀)
    (hblind : ∀ n : ℕ, 2 ≤ n → g (Real.log n) = 0) {N₀ : ℕ} (hN₀ : 2 ≤ N₀) :
    |∫ y, g y * Real.exp (y / 2)| ≤
      2 * C₀ / Real.sqrt N₀ + Real.sqrt N₀ * (∫ y in -Real.log N₀..Real.log N₀, |g y|) +
        Real.sqrt 2 * L / Real.sqrt ((N₀ : ℝ) - 1) := by
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  set Y := Real.log N₀ with hY
  have hY0 : 0 ≤ Y := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N₀))
  have hge : Continuous fun y => g y * Real.exp (y / 2) := hg.mul (by fun_prop)
  have hii : ∀ α β : ℝ, IntervalIntegrable (fun y => g y * Real.exp (y / 2)) volume α β :=
    fun α β => hge.intervalIntegrable α β
  set K₁ : ℕ := ⌈Real.exp (R + 1)⌉₊ with hK₁
  set T₂ : ℝ := Real.log ((N₀ + K₁ : ℕ) : ℝ) with hT₂
  set T₁ : ℝ := R + 1 + Y with hT₁
  have hT₂R : R < T₂ := by
    have h1 : Real.exp (R + 1) ≤ ((N₀ + K₁ : ℕ) : ℝ) := by
      calc Real.exp (R + 1) ≤ K₁ := Nat.le_ceil _
        _ ≤ ((N₀ + K₁ : ℕ) : ℝ) := by push_cast; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    linarith
  have hC0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC 0)
  -- the whole line is an interval
  have hfull : ∫ y, g y * Real.exp (y / 2) = ∫ y in -T₁..T₂, g y * Real.exp (y / 2) := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
    have : R < |y| := by
      rcases hy with h1 | h1
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hR y this, zero_mul]
  have hsplit : ∫ y in -T₁..T₂, g y * Real.exp (y / 2) =
      (∫ y in -T₁..-Y, g y * Real.exp (y / 2)) + (∫ y in -Y..Y, g y * Real.exp (y / 2)) +
        ∫ y in Y..T₂, g y * Real.exp (y / 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _),
      intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have hexpm : Real.exp (-Y / 2) = 1 / Real.sqrt N₀ := by
    rw [show -Y / 2 = -(Y / 2) by ring, Real.exp_neg, Real.exp_half, hY, Real.exp_log hN0,
      one_div]
  have hexpp : Real.exp (Y / 2) = Real.sqrt N₀ := by
    rw [Real.exp_half, hY, Real.exp_log hN0]
  -- left tail
  have hleft : |∫ y in -T₁..-Y, g y * Real.exp (y / 2)| ≤ 2 * C₀ / Real.sqrt N₀ := by
    have hTY : -T₁ ≤ -Y := by linarith
    have hexp : ∫ y in -T₁..-Y, Real.exp (y / 2) =
        2 * (Real.exp (-Y / 2) - Real.exp (-T₁ / 2)) := by
      have := intervalIntegral.integral_comp_div (a := -T₁) (b := -Y) Real.exp
        (by norm_num : (2 : ℝ) ≠ 0)
      rw [this, integral_exp, smul_eq_mul]
    calc |∫ y in -T₁..-Y, g y * Real.exp (y / 2)|
        ≤ ∫ y in -T₁..-Y, |g y * Real.exp (y / 2)| :=
          intervalIntegral.abs_integral_le_integral_abs hTY
      _ ≤ ∫ y in -T₁..-Y, C₀ * Real.exp (y / 2) :=
          intervalIntegral.integral_mono_on hTY (hge.abs.intervalIntegrable _ _)
            ((by fun_prop : Continuous fun y : ℝ => C₀ * Real.exp (y / 2)).intervalIntegrable _ _)
            fun y _ => by
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_right (hC y) (Real.exp_pos _).le
      _ = C₀ * (2 * (Real.exp (-Y / 2) - Real.exp (-T₁ / 2))) := by
          rw [intervalIntegral.integral_const_mul, hexp]
      _ ≤ 2 * C₀ / Real.sqrt N₀ := by
          rw [hexpm]
          have := Real.exp_pos (-T₁ / 2)
          have h2 : C₀ * (2 * (1 / Real.sqrt N₀ - Real.exp (-T₁ / 2))) ≤
              C₀ * (2 * (1 / Real.sqrt N₀)) :=
            mul_le_mul_of_nonneg_left (by linarith) hC0
          calc C₀ * (2 * (1 / Real.sqrt N₀ - Real.exp (-T₁ / 2)))
              ≤ C₀ * (2 * (1 / Real.sqrt N₀)) := h2
            _ = 2 * C₀ / Real.sqrt N₀ := by ring
  -- the window
  have hnear : |∫ y in -Y..Y, g y * Real.exp (y / 2)| ≤
      Real.sqrt N₀ * ∫ y in -Y..Y, |g y| := by
    have hYY : -Y ≤ Y := by linarith
    calc |∫ y in -Y..Y, g y * Real.exp (y / 2)|
        ≤ ∫ y in -Y..Y, |g y * Real.exp (y / 2)| :=
          intervalIntegral.abs_integral_le_integral_abs hYY
      _ ≤ ∫ y in -Y..Y, Real.exp (Y / 2) * |g y| :=
          intervalIntegral.integral_mono_on hYY (hge.abs.intervalIntegrable _ _)
            ((continuous_const.mul hg.abs).intervalIntegrable _ _) fun y hy => by
              rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
              exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hy.2]))
                (abs_nonneg _)
      _ = Real.sqrt N₀ * ∫ y in -Y..Y, |g y| := by
          rw [intervalIntegral.integral_const_mul, hexpp]
  -- the right tail
  have hfar : |∫ y in Y..T₂, g y * Real.exp (y / 2)| ≤
      Real.sqrt 2 * L / Real.sqrt ((N₀ : ℝ) - 1) := by
    refine abs_intervalIntegral_mul_exp_half_le hL hg hN₀ (fun n hn y hy => ?_) K₁
    have hz := hblind n (by omega)
    have hyl : 0 ≤ y - Real.log n := by linarith [hy.1]
    have := hLip y (Real.log n)
    rw [hz, sub_zero, abs_of_nonneg hyl] at this
    exact this
  rw [hfull, hsplit]
  calc |(∫ y in -T₁..-Y, g y * Real.exp (y / 2)) + (∫ y in -Y..Y, g y * Real.exp (y / 2)) +
        ∫ y in Y..T₂, g y * Real.exp (y / 2)|
      ≤ |∫ y in -T₁..-Y, g y * Real.exp (y / 2)| + |∫ y in -Y..Y, g y * Real.exp (y / 2)| +
        |∫ y in Y..T₂, g y * Real.exp (y / 2)| := abs_add_three _ _ _
    _ ≤ 2 * C₀ / Real.sqrt N₀ + Real.sqrt N₀ * (∫ y in -Y..Y, |g y|) +
        Real.sqrt 2 * L / Real.sqrt ((N₀ : ℝ) - 1) := by gcongr

end GaloisForLFunctions.HTGeometry
