import GaloisForLFunctions.RHTower.Sieve.MoebiusLogPowerRealCutoff

open Finset Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Every positive logarithmic Möbius kernel has a global envelope of its sharp degree. -/
theorem exists_abs_moebiusLogPowerKernelReal_succ_le_const_mul_log_pow
    (q : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ Y : ℝ, 1 ≤ Y →
      |moebiusLogPowerKernelReal (q + 1) Y| ≤ D * Real.log Y ^ q := by
  have hlim := tendsto_moebiusLogPowerKernelReal_div_log_pow q
  have hnear : ∀ᶠ Y : ℝ in atTop,
      |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q -
        ((q + 1 : ℕ) : ℝ)| < 1 := by
    exact hlim.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  rw [eventually_atTop] at hnear
  obtain ⟨K₀, hK₀⟩ := hnear
  let K : ℝ := max K₀ 2
  have hK₀K : K₀ ≤ K := le_max_left _ _
  have hKtwo : (2 : ℝ) ≤ K := le_max_right _ _
  let D : ℝ := max (((q + 2 : ℕ) : ℝ))
    ((1 + Real.log K) * Real.log K)
  have hD : 0 ≤ D := by
    exact le_trans (by positivity : 0 ≤ ((q + 2 : ℕ) : ℝ)) (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro Y hY
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  by_cases hKY : K ≤ Y
  · have hYtwo : (2 : ℝ) ≤ Y := hKtwo.trans hKY
    have hlogpos : 0 < Real.log Y := Real.log_pos (by linarith)
    have hclose := hK₀ Y (hK₀K.trans hKY)
    have hratio :
        |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q| ≤
          ((q + 2 : ℕ) : ℝ) := by
      calc
        |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q| ≤
            |moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q -
                ((q + 1 : ℕ) : ℝ)| + |((q + 1 : ℕ) : ℝ)| := by
          simpa only [sub_add_cancel] using abs_add_le
            (moebiusLogPowerKernelReal (q + 1) Y / Real.log Y ^ q -
              ((q + 1 : ℕ) : ℝ)) (((q + 1 : ℕ) : ℝ))
        _ ≤ 1 + ((q + 1 : ℕ) : ℝ) := by
          rw [abs_of_nonneg (by positivity : 0 ≤ ((q + 1 : ℕ) : ℝ))]
          exact add_le_add hclose.le le_rfl
        _ = ((q + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [abs_div, abs_of_pos (pow_pos hlogpos q)] at hratio
    have hsharp : |moebiusLogPowerKernelReal (q + 1) Y| ≤
        ((q + 2 : ℕ) : ℝ) * Real.log Y ^ q := by
      exact (div_le_iff₀ (pow_pos hlogpos q)).mp hratio
    exact hsharp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg hlogY q))
  · have hYK : Y < K := lt_of_not_ge hKY
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    have hlogle : Real.log Y ≤ Real.log K :=
      Real.log_le_log (by positivity) hYK.le
    have hfactor : (1 + Real.log Y) * Real.log Y ≤
        (1 + Real.log K) * Real.log K := by
      exact mul_le_mul (by linarith) hlogle hlogY (by linarith)
    have hglobal :=
      abs_moebiusLogPowerKernelReal_le_one_add_log_mul_pow (q + 1) hY
    calc
      |moebiusLogPowerKernelReal (q + 1) Y| ≤
          (1 + Real.log Y) * Real.log Y ^ (q + 1) := hglobal
      _ = ((1 + Real.log Y) * Real.log Y) * Real.log Y ^ q := by
        rw [pow_succ]
        ring
      _ ≤ ((1 + Real.log K) * Real.log K) * Real.log Y ^ q :=
        mul_le_mul_of_nonneg_right hfactor (pow_nonneg hlogY q)
      _ ≤ D * Real.log Y ^ q :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (pow_nonneg hlogY q)

end

end RHTower.Sieve
