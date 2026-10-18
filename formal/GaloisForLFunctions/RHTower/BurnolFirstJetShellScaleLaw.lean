import GaloisForLFunctions.RHTower.BurnolFirstJetDampingShell
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# The logarithmic boundary mass of the literal Burnol first jet

For every fixed scale ratio `c >= 1`, the complete positive shell has limiting
trace `log(c)/4`. Its action tends strongly to zero. For `c > 1` the nonzero trace
therefore cannot be lost by a trace-norm passage. The dyadic shell is eventually
strictly sub-unit with its original arithmetic normalization.
-/

open Filter Topology ContinuousLinearMap

namespace RHTower
noncomputable section

/-- Exact pole subtraction, with the full analytic Euler remainder retained. -/
theorem re_opTrace_burnolFirstJetDampingShell_eq_regular {c : ℝ} (hc : 1 ≤ c)
    {t : ℝ} (ht : 0 < t) :
    (opTrace (burnolFirstJetDampingShell c hc t)).re = Real.log c / 4 +
      (eulerLogRegular (1 + 2 * t) - eulerLogRegular (1 + 2 * (c * t))) / 4 := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hct : 0 < c * t := mul_pos hc0 ht
  have h1 := eulerLogRegular_eq (by linarith : 1 < 1 + 2 * t)
  have h2 := eulerLogRegular_eq (by linarith : 1 < 1 + 2 * (c * t))
  have hlog : Real.log (2 * (c * t)) = Real.log c + Real.log (2 * t) := by
    rw [show 2 * (c * t) = c * (2 * t) by ring,
      Real.log_mul hc0.ne' (mul_pos two_pos ht).ne']
  simp only [add_sub_cancel_left] at h1 h2
  rw [re_opTrace_burnolFirstJetDampingShell hc ht]
  rw [hlog] at h2
  linarith

/-- The finite boundary mass is fixed by the actual Euler pole, for every scale ratio. -/
theorem tendsto_re_opTrace_burnolFirstJetDampingShell {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun t => (opTrace (burnolFirstJetDampingShell c hc t)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log c / 4)) := by
  have hR := analyticAt_eulerLogRegular.continuousAt
  have h1 : Tendsto (fun t : ℝ => eulerLogRegular (1 + 2 * t))
      (𝓝[>] (0 : ℝ)) (𝓝 (eulerLogRegular 1)) := by
    apply hR.tendsto.comp
    have h : ContinuousAt (fun t : ℝ => 1 + 2 * t) 0 := by fun_prop
    simpa only [mul_zero, add_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t : ℝ => eulerLogRegular (1 + 2 * (c * t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (eulerLogRegular 1)) := by
    apply hR.tendsto.comp
    have h : ContinuousAt (fun t : ℝ => 1 + 2 * (c * t)) 0 := by fun_prop
    simpa only [mul_zero, add_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h : Tendsto (fun t : ℝ => Real.log c / 4 +
      (eulerLogRegular (1 + 2 * t) - eulerLogRegular (1 + 2 * (c * t))) / 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log c / 4)) := by
    simpa only [sub_self, zero_div, add_zero] using
      tendsto_const_nhds.add ((h1.sub h2).div_const 4)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (re_opTrace_burnolFirstJetDampingShell_eq_regular hc ht).symm

/-- Source normalization itself gives a sub-unit shell when `1 < c < exp(4)`. -/
theorem eventually_burnolFirstJetDampingShell_trace_mem_unitInterval {c : ℝ}
    (hc : 1 < c) (hlog : Real.log c < 4) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < (opTrace (burnolFirstJetDampingShell c hc.le t)).re ∧
        (opTrace (burnolFirstJetDampingShell c hc.le t)).re < 1 := by
  have hlim := tendsto_re_opTrace_burnolFirstJetDampingShell hc.le
  have hlo : 0 < Real.log c / 4 := div_pos (Real.log_pos hc) (by norm_num)
  have hhi : Real.log c / 4 < 1 := by linarith
  exact ((tendsto_order.1 hlim).1 0 hlo).and ((tendsto_order.1 hlim).2 1 hhi)

/-- Concrete dyadic source shell: every sufficiently small positive native time is sub-unit. -/
theorem eventually_burnolFirstJetDyadicShell_trace_mem_unitInterval :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < (opTrace (burnolFirstJetDampingShell 2 (by norm_num) t)).re ∧
        (opTrace (burnolFirstJetDampingShell 2 (by norm_num) t)).re < 1 := by
  apply eventually_burnolFirstJetDampingShell_trace_mem_unitInterval (by norm_num : (1 : ℝ) < 2)
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  linarith

/-- Strong disappearance cannot erase the strictly positive limiting nuclear mass. -/
theorem not_tendsto_traceNorm_burnolFirstJetDampingShell_zero {c : ℝ} (hc : 1 < c) :
    ¬ Tendsto (fun t => traceNorm routePBurnolHalfLineL2 (burnolFirstJetDampingShell c hc.le t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  intro hzero
  have hpos : 0 < Real.log c / 4 := div_pos (Real.log_pos hc) (by norm_num)
  have hlo := (tendsto_order.1 (tendsto_re_opTrace_burnolFirstJetDampingShell hc.le)).1
    (Real.log c / 8) (by linarith)
  have hhi := (tendsto_order.1 hzero).2 (Real.log c / 8) (by linarith)
  have hbad : ∀ᶠ t : ℝ in 𝓝[>] 0, False := by
    filter_upwards [hlo, hhi, self_mem_nhdsWithin] with t htlo hthi ht
    have htrace := (le_abs_self (opTrace (burnolFirstJetDampingShell c hc.le t)).re).trans
      ((Complex.abs_re_le_norm _).trans
        (norm_opTrace_le_traceNorm (burnolFirstJetDampingShell_memSchattenClass_one hc.le ht)))
    linarith
  exact hbad.exists.elim fun _ h => h

end
end RHTower
