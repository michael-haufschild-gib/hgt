import GaloisForLFunctions.RHTower.Sieve.ChebyshevPsiBigO
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The exponent-`1/2` estimate for `θ`

`|ψ(x) − θ(x)| ≤ 2√x·log x`, and that difference is far below the contour's own error
`x·exp(−c√(log x))`: writing `L = log x`, the claim `2L·exp(cL^{1/2}) ≤ x^{1/2}` follows from
`2L ≤ x^{1/4}` and `exp(cL^{1/2}) ≤ exp(L/4) = x^{1/4}`, the latter as soon as `L ≥ 16c²`.

So the prime-counting weight `θ` inherits the same error term as `ψ`.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics

/-- The square-root correction is below the contour's error term. -/
theorem sqrt_mul_log_le_shape {c : ℝ} (hc0 : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt x * Real.log x ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).def
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hlog, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (16 * c ^ 2))] with x hx hx1 hL
  have hx0 : (0 : ℝ) < x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hL
  have hLc : 16 * c ^ 2 ≤ Real.log x := le_trans (le_max_right _ _) hL
  have hquarter : (0 : ℝ) < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  -- `2 log x ≤ x^{1/4}`
  have hA : 2 * Real.log x ≤ x ^ ((1 : ℝ) / 4) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_pos hquarter] at hx
    linarith
  -- `exp(c√(log x)) ≤ x^{1/4}`
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hs : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt (by linarith)
  have hsc : 4 * c ≤ Real.sqrt (Real.log x) := by
    nlinarith [hs, hs0, hLc, hc0]
  have hB : Real.exp (c * Real.sqrt (Real.log x)) ≤ x ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hsc, hs, hs0, hc0]
  -- combine
  have hprod : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hexp0 : (0 : ℝ) < Real.exp (c * Real.sqrt (Real.log x)) := Real.exp_pos _
  have hkey : 2 * Real.log x * Real.exp (c * Real.sqrt (Real.log x)) ≤ Real.sqrt x := by
    calc 2 * Real.log x * Real.exp (c * Real.sqrt (Real.log x))
        ≤ x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) :=
          mul_le_mul hA hB hexp0.le hquarter.le
      _ = Real.sqrt x := hprod
  -- divide through by the exponential
  have hneg : Real.exp (-c * Real.sqrt (Real.log x))
      = (Real.exp (c * Real.sqrt (Real.log x)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hinv0 : (0 : ℝ) < (Real.exp (c * Real.sqrt (Real.log x)))⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right hkey hinv0.le
  have hcancel : 2 * Real.log x * Real.exp (c * Real.sqrt (Real.log x))
      * (Real.exp (c * Real.sqrt (Real.log x)))⁻¹ = 2 * Real.log x := by
    field_simp
  have hstep : 2 * Real.log x
      ≤ Real.sqrt x * (Real.exp (c * Real.sqrt (Real.log x)))⁻¹ := by
    linarith [hmul, hcancel]
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  rw [hneg]
  nlinarith [mul_le_mul_of_nonneg_left hstep hsx, hxx]

/-- **The prime number theorem for `θ` with a square-root-logarithmic error term.** -/
theorem chebyshevTheta_sub_id_isBigO :
    ∃ c > 0, (Chebyshev.theta - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc0, hpsi⟩ := chebyshevPsi_sub_id_isBigO
  refine ⟨c, hc0, ?_⟩
  have hdiff : (Chebyshev.theta - id)
      = (Chebyshev.theta - Chebyshev.psi) + (Chebyshev.psi - id) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hdiff]
  refine Asymptotics.IsBigO.add (Asymptotics.IsBigO.of_bound 1 ?_) hpsi
  filter_upwards [sqrt_mul_log_le_shape hc0, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hcomp := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hgnorm : ‖x * Real.exp (-c * Real.sqrt (Real.log x))‖
      = x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Pi.sub_apply, Real.norm_eq_abs, hgnorm, one_mul, abs_sub_comm]
  linarith [hcomp, hx]

end RHTower.Sieve
