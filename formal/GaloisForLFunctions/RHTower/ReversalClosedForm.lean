/-
Doc 40 §2 / doc 41 (task #147): the c = 2 closed form of the continuum
reversal, machine-checked.

The reversal integrand at c = 2, s = 0 is the rational function
`8 x^(2 : ℕ) / (4 - x^(2 : ℕ))^(2 : ℕ)`; its antiderivative on (-2, 2) is
`4 x / (4 - x^(2 : ℕ)) - (log (2+x) - log (2-x))`, so the edge reversal is
`R(1/2, 2, 0) = ∫_0^(1 : ℕ) = 4/3 - log 3`, and the march cushion survives:
`4/3 - log 3 < 1/4` (via `log 3 > 13/12`, i.e. `e^{13/12} < 3`).  These are
the numerical capstones consumed by the Theorem B⁗ march shells
(`LedgerConvex`): the reversal budget at the (F1) edge is below a quarter.
-/
import Mathlib

namespace RHTower

open Real

noncomputable def reversalAntideriv (x : ℝ) : ℝ :=
  4 * x / (4 - x ^ (2 : ℕ)) - (Real.log (2 + x) - Real.log (2 - x))

theorem reversalAntideriv_zero : reversalAntideriv 0 = 0 := by
  simp [reversalAntideriv]

/-- The antiderivative identity behind doc 40 §2, on the open interval. -/
theorem hasDerivAt_reversalAntideriv {x : ℝ} (hx2 : x ^ (2 : ℕ) < 4) :
    HasDerivAt reversalAntideriv (8 * x ^ (2 : ℕ) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ)) x := by
  have hden : 4 - x ^ (2 : ℕ) ≠ 0 := by nlinarith
  have hp : 0 < 2 + x := by nlinarith
  have hm : 0 < 2 - x := by nlinarith
  have h1 : HasDerivAt (fun y : ℝ => 4 * y / (4 - y ^ (2 : ℕ)))
      ((4 * (4 - x ^ (2 : ℕ)) - 4 * x * (-(2 * x))) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ)) x := by
    have hu : HasDerivAt (fun y : ℝ => 4 * y) 4 x := by
      simpa using (hasDerivAt_id x).const_mul (4 : ℝ)
    have hv : HasDerivAt (fun y : ℝ => 4 - y ^ (2 : ℕ)) (-(2 * x)) x := by
      have := (hasDerivAt_pow 2 x).const_sub (4 : ℝ)
      simpa [pow_one] using this
    exact hu.div hv hden
  have h2 : HasDerivAt (fun y : ℝ => Real.log (2 + y)) (1 / (2 + x)) x := by
    have hin : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (2 : ℝ)
    simpa [one_div] using hin.log hp.ne'
  have h3 : HasDerivAt (fun y : ℝ => Real.log (2 - y)) (-(1 / (2 - x))) x := by
    have hin : HasDerivAt (fun y : ℝ => 2 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (2 : ℝ)
    have := hin.log hm.ne'
    simpa [neg_div, one_div] using this
  have h := h1.sub (h2.sub h3)
  have harith : (4 * (4 - x ^ (2 : ℕ)) - 4 * x * (-(2 * x))) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ)
      - (1 / (2 + x) - -(1 / (2 - x))) = 8 * x ^ (2 : ℕ) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ) := by
    have h4 : (4 : ℝ) - x ^ (2 : ℕ) = (2 + x) * (2 - x) := by ring
    field_simp
    ring
  rw [harith] at h
  exact h

/-- The reversal integrand is continuous away from the poles. -/
theorem continuousOn_reversal_integrand :
    ContinuousOn (fun x : ℝ => 8 * x ^ (2 : ℕ) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ))
      (Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    have h1 : x ^ (2 : ℕ) ≤ 1 := by
      rcases hx with ⟨h0, h1⟩
      nlinarith
    have h2 : (0 : ℝ) < 4 - x ^ (2 : ℕ) := by nlinarith
    positivity

/-- **Doc 40 §2, machine-checked**: the edge reversal in closed form. -/
theorem reversal_integral_eq_closed_form :
    (∫ x in (0 : ℝ)..1, 8 * x ^ (2 : ℕ) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ)) = 4 / 3 - Real.log 3 := by
  have hFTC :
      (∫ x in (0 : ℝ)..1, 8 * x ^ (2 : ℕ) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ))
        = reversalAntideriv 1 - reversalAntideriv 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      have hx2 : x ^ (2 : ℕ) < 4 := by
        rcases hx with ⟨h0, h1⟩
        nlinarith
      exact hasDerivAt_reversalAntideriv hx2
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact continuousOn_reversal_integrand
  rw [hFTC, reversalAntideriv_zero]
  have h3 : (2 : ℝ) + 1 = 3 := by norm_num
  have h1 : (2 : ℝ) - 1 = 1 := by norm_num
  simp [reversalAntideriv, h3, h1, Real.log_one]
  norm_num

/-- `e^{13/12} < 3`, by `e < 2.7182818286` and `e^{1/12} ≤ 12/11`. -/
theorem exp_thirteen_twelfths_lt_three : Real.exp (13 / 12) < 3 := by
  have hsplit : Real.exp ((13 : ℝ) / 12) = Real.exp 1 * Real.exp (1 / 12) := by
    rw [← Real.exp_add]; norm_num
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlow : (11 : ℝ) / 12 ≤ Real.exp (-(1 / 12)) := by
    have := Real.add_one_le_exp (-(1 / 12) : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp (1 / 12) := Real.exp_pos _
  have hprod : Real.exp (-(1 / 12)) * Real.exp (1 / 12) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hup : Real.exp ((1 : ℝ) / 12) ≤ 12 / 11 := by
    nlinarith [mul_le_mul_of_nonneg_right hlow hpos.le]
  calc Real.exp ((13 : ℝ) / 12) = Real.exp 1 * Real.exp (1 / 12) := hsplit
    _ ≤ Real.exp 1 * (12 / 11) := by
        exact mul_le_mul_of_nonneg_left hup (Real.exp_pos 1).le
    _ < 2.7182818286 * (12 / 11) := by
        have : (0 : ℝ) < 12 / 11 := by norm_num
        exact mul_lt_mul_of_pos_right h1 this
    _ < 3 := by norm_num

theorem log_three_gt_thirteen_twelfths : (13 : ℝ) / 12 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
  exact exp_thirteen_twelfths_lt_three

/-- **The march-cushion capstone**: the edge reversal is below one quarter. -/
theorem reversal_edge_lt_quarter : (4 : ℝ) / 3 - Real.log 3 < 1 / 4 := by
  have := log_three_gt_thirteen_twelfths
  linarith

/-- Integral form of the capstone, as consumed by the B⁗ march shells. -/
theorem reversal_integral_lt_quarter :
    (∫ x in (0 : ℝ)..1, 8 * x ^ (2 : ℕ) / (4 - x ^ (2 : ℕ)) ^ (2 : ℕ)) < 1 / 4 := by
  rw [reversal_integral_eq_closed_form]
  exact reversal_edge_lt_quarter

end RHTower
