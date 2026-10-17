import GaloisForLFunctions.BiScaleUncertainty.IntegerBlockVarianceBridge

/-!
# Exact arithmetic quadrature of the window Laplace energy

On the Nyquist cell `[log n, log(n+1))` the causal response is
`R_N(t) = e^{−t/2}(ψ(n) + 1 − t − e^t)`, so its squared integral over the cell has the closed form

`∫_{log n}^{log(n+1)} e^{−t}(c + 1 − t − e^t)² dt = F_c(log(n+1)) − F_c(log n)`,
`F_c(t) = −e^{−t}((c+1−t)² − 2(c+1−t) + 2) − 2(c+1)t + t² + e^t`,  `c = ψ(n)`.

Summing over the cells `n = 1, …, N+1` gives the window Laplace energy

`∫_0^L R_N² = Σ_{n=1}^{N+1} (F_{ψ(n)}(log(n+1)) − F_{ψ(n)}(log n))`,

an explicit quadratic form in the values `ψ(n)` with coefficient `1/(n(n+1))` on `ψ(n)²`: the
Wall-1 energy of the field as a finite arithmetic expression, ready for the producer machinery of
floor sums and Stirling bounds.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-- The cell antiderivative `F_c(t) = −e^{−t}((c+1−t)² − 2(c+1−t) + 2) − 2(c+1)t + t² + e^t`. -/
def cellWindowPrimitive (c t : ℝ) : ℝ :=
  -Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) - 2 * (c + 1) * t + t ^ 2 + Real.exp t

theorem hasDerivAt_cellWindowPrimitive (c t : ℝ) :
    HasDerivAt (cellWindowPrimitive c) (Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-t)) t := by
    have h0 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t :=
      ((hasDerivAt_neg t).exp).neg
    exact h0.congr_deriv (by ring)
  have ha : HasDerivAt (fun t : ℝ => c + 1 - t) (-1) t := (hasDerivAt_id t).const_sub (c + 1)
  have h2 : HasDerivAt (fun t : ℝ => (c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2)
      (-2 * (c + 1 - t) + 2) t := by
    have := ((ha.pow 2).sub (ha.const_mul 2)).add_const 2
    refine this.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun t : ℝ => -2 * (c + 1) * t + t ^ 2 + Real.exp t)
      (-2 * (c + 1) + 2 * t + Real.exp t) t := by
    have := (((hasDerivAt_id t).const_mul (-2 * (c + 1))).add (hasDerivAt_pow 2 t)).add
      (Real.hasDerivAt_exp t)
    refine this.congr_deriv ?_
    norm_num
  have h : HasDerivAt (fun t : ℝ => -Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) +
      (-2 * (c + 1) * t + t ^ 2 + Real.exp t))
      (Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) +
        -Real.exp (-t) * (-2 * (c + 1 - t) + 2) + (-2 * (c + 1) + 2 * t + Real.exp t)) t :=
    (h1.mul h2).add h3
  have hfun : cellWindowPrimitive c = fun t : ℝ =>
      -Real.exp (-t) * ((c + 1 - t) ^ 2 - 2 * (c + 1 - t) + 2) +
        (-2 * (c + 1) * t + t ^ 2 + Real.exp t) := by
    funext t; unfold cellWindowPrimitive; ring
  rw [hfun]
  refine h.congr_deriv ?_
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (2 * (c + 1 - t) - Real.exp t) * hexp

/-- **Closed-form cell energy:**
`∫_{log n}^{log(n+1)} e^{−t}(c + 1 − t − e^t)² = F_c(log(n+1)) − F_c(log n)`. -/
theorem integral_cell_window_sq (c : ℝ) (n : ℕ) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2) =
      cellWindowPrimitive c (Real.log ((n : ℝ) + 1)) - cellWindowPrimitive c (Real.log (n : ℝ)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_cellWindowPrimitive c t)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t) * (c + 1 - t - Real.exp t) ^ 2).intervalIntegrable
      _ _)

/-- The explicit value of the cell antiderivative at `log m`. -/
theorem cellWindowPrimitive_log (c : ℝ) {m : ℝ} (hm : 0 < m) :
    cellWindowPrimitive c (Real.log m) =
      -((c + 1 - Real.log m) ^ 2 - 2 * (c + 1 - Real.log m) + 2) / m -
        2 * (c + 1) * Real.log m + Real.log m ^ 2 + m := by
  unfold cellWindowPrimitive
  rw [Real.exp_neg, Real.exp_log hm]
  ring

/-- On the cell of `n` inside the window, the causal response is `e^{−t/2}(ψ(n) + 1 − t − e^t)`. -/
theorem causalResponse_sq_eq_on_cell (N : ℕ) {n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N + 2) {t : ℝ}
    (ht : t ∈ Ico (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :
    causalResponse N t ^ 2 =
      Real.exp (-t) * (Chebyshev.psi (n : ℝ) + 1 - t - Real.exp t) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ t := (Real.log_nonneg (by exact_mod_cast hn)).trans ht.1
  have htL : t ≤ cutoff N := by
    refine ht.2.le.trans ?_
    unfold cutoff
    exact Real.log_le_log (by positivity) (by exact_mod_cast hnN)
  rw [causalResponse_eq_on_window N ht0 htL]
  unfold normalizedLogError logError
  rw [Chebyshev.psi_eq_psi_coe_floor (Real.exp t), floor_exp_eq_of_mem_cell hn ht]
  have he : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have : Real.exp (-t / 2) * (Chebyshev.psi (n : ℝ) - Real.exp t) + (1 - t) * Real.exp (-t / 2) =
      Real.exp (-t / 2) * (Chebyshev.psi (n : ℝ) + 1 - t - Real.exp t) := by ring
  rw [this, mul_pow, he]

/-- The cell energy of the causal response in closed form. -/
theorem integral_cell_causalResponse_sq (N : ℕ) {n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N + 2) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), causalResponse N t ^ 2) =
      cellWindowPrimitive (Chebyshev.psi (n : ℝ)) (Real.log ((n : ℝ) + 1)) -
        cellWindowPrimitive (Chebyshev.psi (n : ℝ)) (Real.log (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  rw [← integral_cell_window_sq (Chebyshev.psi (n : ℝ)) n]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ Real.log ((n : ℝ) + 1) := by
    rw [ae_iff]; simp
  filter_upwards [hne] with t ht hmem
  rw [uIoc_of_le hle] at hmem
  exact causalResponse_sq_eq_on_cell N hn hnN ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩

/-- **The window Laplace energy as a finite arithmetic quadrature:**
`∫_0^L R_N² = Σ_{n=1}^{N+1} (F_{ψ(n)}(log(n+1)) − F_{ψ(n)}(log n))`. -/
theorem integral_sq_causalResponse_window_eq_sum (N : ℕ) :
    (∫ t in Icc 0 (cutoff N), causalResponse N t ^ 2) =
      ∑ k ∈ Finset.range (N + 1),
        (cellWindowPrimitive (Chebyshev.psi ((k + 1 : ℕ) : ℝ)) (Real.log (((k + 1 : ℕ) : ℝ) + 1)) -
          cellWindowPrimitive (Chebyshev.psi ((k + 1 : ℕ) : ℝ)) (Real.log ((k + 1 : ℕ) : ℝ))) := by
  have hL0 : 0 ≤ cutoff N := cutoff_nonneg N
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t => causalResponse N t ^ 2) (μ := volume)
    (a := fun k : ℕ => Real.log ((k : ℝ) + 1)) (n := N + 1)
    (fun k _ => (integrable_sq_causalResponse N).intervalIntegrable)
  have ha0 : Real.log ((0 : ℕ) + 1 : ℝ) = 0 := by simp
  have haN : Real.log (((N + 1 : ℕ) : ℝ) + 1) = cutoff N := by
    unfold cutoff; congr 1; push_cast; ring
  rw [ha0, haN] at hsum
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL0, ← hsum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hkN : k + 1 + 1 ≤ N + 2 := by have := Finset.mem_range.mp hk; omega
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [← integral_cell_causalResponse_sq N hk1 hkN, hcast]

/-- The full Laplace energy in closed arithmetic form (window quadrature plus endpoint term). -/
theorem laplaceEnergy_eq_sum_add_endpoint (N : ℕ) :
    laplaceEnergy N =
      (∑ k ∈ Finset.range (N + 1),
        (cellWindowPrimitive (Chebyshev.psi ((k + 1 : ℕ) : ℝ)) (Real.log (((k + 1 : ℕ) : ℝ) + 1)) -
          cellWindowPrimitive (Chebyshev.psi ((k + 1 : ℕ) : ℝ)) (Real.log ((k + 1 : ℕ) : ℝ)))) +
        causalResponse N (cutoff N) ^ 2 := by
  rw [← integral_sq_causalResponse_window_eq_sum, ← integral_sq_causalResponse_eq_laplaceEnergy,
    integral_sq_causalResponse_eq_window_add_tail]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [causalResponse_eq_on_window N ht.1 ht.2]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
