import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation

/-!
# The moving-window mean of a separated trigonometric packet

Every nonzero frequency integrates to at most `2/|β|` over a window of any length and position, so a
trigonometric polynomial whose nonzero frequencies are all at least `β` apart from zero has window
mean at most the number of modes times the coefficient ceiling times `2/(Tβ)`.

Adding back a constant term, the window mean of a packet with constant coefficient `μ` is at least
`μ` minus that error: a long enough window sees the constant coefficient and nothing else.
-/

open intervalIntegral

namespace GaloisForLFunctions.HTGeometry

section WindowMean

variable {ι : Type*} [Fintype ι]

theorem intervalIntegrable_exp_mode (β : ℝ) (u T : ℝ) :
    IntervalIntegrable (fun t : ℝ => Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I)) MeasureTheory.volume
      u (u + T) := by
  have hcont : Continuous fun t : ℝ => Complex.exp ((t : ℂ) * (β : ℂ) * Complex.I) := by
    fun_prop
  exact hcont.intervalIntegrable u (u + T)

/-- **`(17)` aggregated.**  The window mean of a trigonometric packet with separated nonzero
frequencies is small. -/
theorem norm_window_mean_le (c : ι → ℂ) (β : ι → ℝ) {βmin μ T : ℝ} (hβmin : 0 < βmin)
    (hβ : ∀ i, βmin ≤ |β i|) (hμ : 0 ≤ μ) (hc : ∀ i, ‖c i‖ ≤ μ) (hT : 0 < T) (u : ℝ) :
    ‖(1 / (T : ℂ)) * ∫ t in u..(u + T), ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖
      ≤ (Fintype.card ι : ℝ) * μ * (2 / (T * βmin)) := by
  classical
  have hsplit : (∫ t in u..(u + T), ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I))
      = ∑ i, c i * ∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
    · exact fun i _ => (intervalIntegrable_exp_mode (β i) u T).const_mul (c i)
  have hterm : ∀ i : ι,
      ‖c i * ∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖
        ≤ μ * (2 / βmin) := by
    intro i
    have hβi : β i ≠ 0 := by
      intro h
      have := hβ i
      rw [h, abs_zero] at this
      exact absurd this (not_le.mpr hβmin)
    have hosc := norm_integral_exp_window_le hβi u T
    have hmono : 2 / |β i| ≤ 2 / βmin := by
      refine div_le_div_of_nonneg_left (by norm_num) hβmin (hβ i)
    rw [norm_mul]
    calc ‖c i‖ * ‖∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖
        ≤ μ * (2 / |β i|) :=
          mul_le_mul (hc i) hosc (norm_nonneg _) hμ
      _ ≤ μ * (2 / βmin) := mul_le_mul_of_nonneg_left hmono hμ
  have hsum : ‖∑ i, c i * ∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖
      ≤ (Fintype.card ι : ℝ) * (μ * (2 / βmin)) := by
    calc ‖∑ i, c i * ∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖
        ≤ ∑ i, ‖c i * ∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : ι, μ * (2 / βmin) := Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card ι : ℝ) * (μ * (2 / βmin)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsplit, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hT)]
  calc 1 / T * ‖∑ i, c i * ∫ t in u..(u + T), Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)‖
      ≤ 1 / T * ((Fintype.card ι : ℝ) * (μ * (2 / βmin))) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        positivity
    _ = (Fintype.card ι : ℝ) * μ * (2 / (T * βmin)) := by
        field_simp

/-- **`(18)`.**  A packet with constant coefficient `μ` and separated nonzero modes has window mean
at least `μ` minus the aggregate oscillation error. -/
theorem window_mean_ge (c : ι → ℂ) (β : ι → ℝ) {βmin μ T : ℝ} (hβmin : 0 < βmin)
    (hβ : ∀ i, βmin ≤ |β i|) (hcbound : ℝ) (hcnn : 0 ≤ hcbound) (hc : ∀ i, ‖c i‖ ≤ hcbound)
    (hT : 0 < T) (u : ℝ) :
    (μ : ℝ) - (Fintype.card ι : ℝ) * hcbound * (2 / (T * βmin))
      ≤ ((1 / (T : ℂ)) * ∫ t in u..(u + T),
          ((μ : ℂ) + ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I))).re := by
  classical
  have hconst : (∫ t in u..(u + T), (μ : ℂ)) = (T : ℂ) * (μ : ℂ) := by
    rw [intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul, mul_comm]
  have hsum : (∫ t in u..(u + T),
      ((μ : ℂ) + ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I)))
      = (T : ℂ) * (μ : ℂ)
        + ∫ t in u..(u + T), ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I) := by
    have hint : IntervalIntegrable
        (fun t : ℝ => ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I))
        MeasureTheory.volume u (u + T) := by
      have : ∀ i : ι, IntervalIntegrable
          (fun t : ℝ => c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I))
          MeasureTheory.volume u (u + T) :=
        fun i => (intervalIntegrable_exp_mode (β i) u T).const_mul (c i)
      have hcont : Continuous fun t : ℝ =>
          ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I) := by
        refine continuous_finsetSum _ fun i _ => ?_
        fun_prop
      exact hcont.intervalIntegrable u (u + T)
    rw [intervalIntegral.integral_add (intervalIntegrable_const) hint, hconst]
  have hTne : (T : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hT
  have hmain := norm_window_mean_le c β hβmin hβ hcnn hc hT u
  set E : ℂ := (1 / (T : ℂ)) * ∫ t in u..(u + T),
    ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I) with hE
  have hval : ((1 / (T : ℂ)) * ∫ t in u..(u + T),
      ((μ : ℂ) + ∑ i, c i * Complex.exp ((t : ℂ) * (β i : ℂ) * Complex.I))) = (μ : ℂ) + E := by
    rw [hsum, mul_add, hE]
    congr 1
    field_simp
  rw [hval, Complex.add_re, Complex.ofReal_re]
  have hreal : -(Fintype.card ι : ℝ) * hcbound * (2 / (T * βmin)) ≤ E.re := by
    have h1 : |E.re| ≤ ‖E‖ := Complex.abs_re_le_norm E
    have h2 : ‖E‖ ≤ (Fintype.card ι : ℝ) * hcbound * (2 / (T * βmin)) := hmain
    have := abs_le.mp (le_trans h1 h2)
    linarith [this.1]
  linarith

end WindowMean

end GaloisForLFunctions.HTGeometry
