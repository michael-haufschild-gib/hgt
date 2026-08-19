import GaloisForLFunctions.HTGeometry.OddEulerCombTemperedAdmissionWall

/-!
# A constant times a power times a polylogarithm is eventually below a larger power

The three schedule thresholds of `Sieve/RouteTScheduleWorstCase` all have the shape

`C·L^α·(1 + |log L|)^k ≤ L^β`,  `α < β`,

so one lemma discharges them all.  It splits `L^β = L^α·L^{(β−α)/2}·L^{(β−α)/2}` and spends the two
halves on the constant and on the polylogarithm, the latter through
`HTGeometry.eventually_one_add_abs_log_pow_le_rpow`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **A power times a polylogarithm is eventually below any larger power.** -/
theorem eventually_const_mul_rpow_polylog_le_rpow {C α β : ℝ} (k : ℕ) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop, C * L ^ α * (1 + |Real.log L|) ^ k ≤ L ^ β := by
  have hhalf : (0 : ℝ) < (β - α) / 2 := by linarith
  have hgrow : Tendsto (fun L : ℝ => L ^ ((β - α) / 2)) atTop atTop := tendsto_rpow_atTop hhalf
  filter_upwards [HTGeometry.eventually_one_add_abs_log_pow_le_rpow k hhalf,
    hgrow.eventually_ge_atTop C, Filter.eventually_ge_atTop (1 : ℝ)] with L hpoly hconst hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hα0 : (0 : ℝ) ≤ L ^ α := Real.rpow_nonneg hL0.le _
  have hpoly0 : (0 : ℝ) ≤ (1 + |Real.log L|) ^ k := by positivity
  have hsplit : L ^ β = L ^ α * L ^ ((β - α) / 2) * L ^ ((β - α) / 2) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    ring_nf
  rw [hsplit]
  have h1 : C * L ^ α ≤ L ^ ((β - α) / 2) * L ^ α := by
    have := mul_le_mul_of_nonneg_right hconst hα0
    linarith [this]
  have hhalf0 : (0 : ℝ) ≤ L ^ ((β - α) / 2) := Real.rpow_nonneg hL0.le _
  have hstep : C * L ^ α * (1 + |Real.log L|) ^ k
      ≤ (L ^ ((β - α) / 2) * L ^ α) * (1 + |Real.log L|) ^ k :=
    mul_le_mul_of_nonneg_right h1 hpoly0
  refine hstep.trans ?_
  have hstep2 : (L ^ ((β - α) / 2) * L ^ α) * (1 + |Real.log L|) ^ k
      ≤ (L ^ ((β - α) / 2) * L ^ α) * L ^ ((β - α) / 2) := by
    refine mul_le_mul_of_nonneg_left hpoly ?_
    positivity
  refine hstep2.trans (le_of_eq ?_)
  ring

/-- **The Chebyshev threshold of the schedule.** -/
theorem eventually_cheb_threshold :
    ∀ᶠ L : ℝ in atTop, Real.log (216 * (2 + L)) ≤ L ^ (0.99 : ℝ) / 4 := by
  have hkey := eventually_const_mul_rpow_polylog_le_rpow (C := 872) (α := (0 : ℝ))
    (β := (0.99 : ℝ)) 1 (by norm_num)
  filter_upwards [hkey, Filter.eventually_ge_atTop (Real.exp 1)] with L hK hLe
  have hL1 : (1 : ℝ) ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hlog1 : (1 : ℝ) ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at this
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
  rw [Real.rpow_zero, mul_one, habs] at hK
  have h216 : Real.log 216 ≤ 216 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 216 by norm_num)
    linarith
  have hlog3 : Real.log 3 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith
  have hle : (2 : ℝ) + L ≤ 3 * L := by linarith
  have hlog : Real.log (216 * (2 + L)) ≤ 216 + 3 + Real.log L := by
    have h1 : Real.log (216 * (2 + L)) ≤ Real.log (216 * (3 * L)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (216 * (3 * L)) = Real.log 216 + Real.log 3 + Real.log L := by
      rw [show (216 : ℝ) * (3 * L) = 216 * 3 * L by ring,
        Real.log_mul (by norm_num) (ne_of_gt hL0), Real.log_mul (by norm_num) (by norm_num)]
    linarith [h1, h2.le, h2.ge]
  have hpow : (872 : ℝ) * (1 + Real.log L) ^ 1 ≤ L ^ (0.99 : ℝ) := hK
  simp only [pow_one] at hpow
  linarith

end

end RHTower.Sieve
