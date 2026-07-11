import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.SeamRealAxisGrowth
import GaloisForLFunctions.RHTower.LittlewoodXi

/-!
# The completed Riemann ξ has order ≤ 1

The entire completion `ξ(s) = s(s-1)/2 · Λ₀(s) + ½`, with `Λ₀ = completedRiemannZeta₀` the entire
completed zeta, obeys the Hadamard order-one growth bound

`‖ξ(s)‖ ≤ exp (C · (1 + ‖s‖) · log (2 + ‖s‖))`.

All of the transcendental growth is carried by the entire function `Λ₀`: multiplying by the
degree-two polynomial `s(s-1)/2` and adding the constant `½` enlarge the exponent by only a bounded
amount.  This file proves the reduction from the explicit `CompletedZeta0OrderOne` interface; the
unconditional producer and public premise-free theorem live in `CompletedZetaGrowth`.
-/

open Complex Real

namespace RHTower

/-- Order-one growth of the entire completed zeta `Λ₀ = completedRiemannZeta₀`: for a uniform
constant `C > 0`, `‖Λ₀ s‖ ≤ exp (C · (1 + ‖s‖) · log (2 + ‖s‖))` for all `s`.  This is the analytic
content of "`Λ₀` is entire of order ≤ 1" written in the explicit form Hadamard theory consumes. -/
def CompletedZeta0OrderOne : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
    ‖completedRiemannZeta₀ s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))

/-- A polynomial in `r ≥ 0` is dominated by the order-one exponential envelope: concretely
`2(1+r)² ≤ exp (3·(1+r)·log(2+r))`.  Since `exp((1+r)log(2+r)) ≥ 2+r`, cubing gives
`exp(3·(1+r)log(2+r)) ≥ (2+r)³ ≥ 2(1+r)²`. -/
private lemma two_mul_sq_le_exp_growth (r : ℝ) (hr : 0 ≤ r) :
    2 * (1 + r) ^ 2 ≤ Real.exp (3 * ((1 + r) * Real.log (2 + r))) := by
  set P : ℝ := (1 + r) * Real.log (2 + r) with hP
  have hlog : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hPge : Real.log (2 + r) ≤ P := by
    rw [hP]; exact le_mul_of_one_le_left hlog (by linarith)
  have hEP : 2 + r ≤ Real.exp P := by
    calc 2 + r = Real.exp (Real.log (2 + r)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp P := Real.exp_le_exp.mpr hPge
  have hexp3 : Real.exp (3 * P) = Real.exp P ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul]
  have h2r0 : (0 : ℝ) ≤ 2 + r := by linarith
  have hcube : (2 + r) ^ 3 ≤ Real.exp P ^ 3 := by gcongr
  rw [hexp3]
  nlinarith [hcube, hr, mul_nonneg (mul_nonneg hr hr) hr, sq_nonneg r]

/-- **The completed Riemann ξ has order ≤ 1.**  Given the order-one growth of the entire completed
zeta `Λ₀` (`CompletedZeta0OrderOne`), the completion `ξ = s(s-1)/2·Λ₀ + ½` obeys the Hadamard
order-one bound `‖ξ s‖ ≤ exp (C·(1+‖s‖)·log(2+‖s‖))`.  The polynomial prefactor `s(s-1)/2` and the
constant `½` add only a bounded amount to the exponent, so the same functional form persists with a
larger constant. -/
theorem xi_growth_order_le_one_of_completedZeta0OrderOne (h : CompletedZeta0OrderOne) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖xi s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C + 3, by linarith, fun s => ?_⟩
  set r : ℝ := ‖s‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg s
  set P : ℝ := (1 + r) * Real.log (2 + r) with hP
  have hP0 : 0 ≤ P := by
    rw [hP]; exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  -- the completed-zeta input, rewritten with `r` and `P`
  have hL : ‖completedRiemannZeta₀ s‖ ≤ Real.exp (C * P) := by
    have hbs := hbound s
    rw [← hr, mul_assoc, ← hP] at hbs
    exact hbs
  -- envelope facts
  have henv : 2 * (1 + r) ^ 2 ≤ Real.exp (3 * P) := by
    rw [hP]; exact two_mul_sq_le_exp_growth r hr0
  have hexpCP : (1 : ℝ) ≤ Real.exp (C * P) := Real.one_le_exp (mul_nonneg hC.le hP0)
  -- polynomial prefactor bound
  have hpre : ‖s * (s - 1) / 2‖ ≤ r * (r + 1) / 2 := by
    have e : ‖s * (s - 1) / 2‖ = ‖s‖ * ‖s - 1‖ / 2 := by
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    rw [e, ← hr]
    have hs1 : ‖s - 1‖ ≤ r + 1 := by
      have := norm_sub_le s 1
      rw [← hr] at this
      simpa using this
    linarith [mul_le_mul_of_nonneg_left hs1 hr0]
  -- norm decomposition of ξ
  have hxieq : xi s = s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2 := rfl
  have hxi : ‖xi s‖ ≤ (r * (r + 1) / 2) * ‖completedRiemannZeta₀ s‖ + 1 / 2 := by
    rw [hxieq]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have key := mul_le_mul_of_nonneg_right hpre (norm_nonneg (completedRiemannZeta₀ s))
    linarith [key]
  -- rewrite the goal exponent and split the exponential
  have hgoalexp : (C + 3) * (1 + r) * Real.log (2 + r) = C * P + 3 * P := by rw [hP]; ring
  rw [hgoalexp, Real.exp_add]
  -- final chain
  set A : ℝ := Real.exp (C * P) with hA
  set B : ℝ := Real.exp (3 * P) with hB
  set L : ℝ := ‖completedRiemannZeta₀ s‖ with hLdef
  have hpre0 : (0 : ℝ) ≤ r * (r + 1) / 2 := by nlinarith [hr0]
  calc ‖xi s‖
      ≤ (r * (r + 1) / 2) * L + 1 / 2 := hxi
    _ ≤ (r * (r + 1) / 2) * A + 1 / 2 := by
        linarith [mul_le_mul_of_nonneg_left hL hpre0]
    _ ≤ (r * (r + 1) / 2) * A + (1 / 2) * A := by nlinarith [hexpCP]
    _ = ((r * (r + 1) / 2) + 1 / 2) * A := by ring
    _ ≤ B * A := by
        apply mul_le_mul_of_nonneg_right _ (by linarith [hexpCP] : (0 : ℝ) ≤ A)
        nlinarith [henv, hr0, sq_nonneg r]
    _ = A * B := by ring

end RHTower
