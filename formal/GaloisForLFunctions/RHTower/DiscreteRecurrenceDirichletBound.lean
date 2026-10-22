import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence

/-!
# The Dirichlet half of the discrete recurrence exponent

The first integer time at which every projective phase of a spectrum returns to within `r` of an
integer is at most `(1/r + 2)^d`, by simultaneous Dirichlet approximation in `d` coordinates.  So
the recurrence exponent is at most the number of independent phases, for *every* spectrum, with no
genericity and no metric theory.

This is the upper half of the sharp exponent law; the matching lower bound holds only almost
everywhere and is the Diophantine side.
-/

open Filter
open scoped Topology

namespace RHTower

/-- The first positive integer time at which every phase is within `r` of an integer. -/
noncomputable def discreteRecurrenceTime {d : ℕ} (α : Fin d → ℝ) (r : ℝ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∀ i, ∃ m : ℤ, |(n : ℝ) * α i - m| ≤ r}

/-- **Dirichlet bound.**  The recurrence time is at most the pigeonhole cost `(⌈1/r⌉ + 1)^d`. -/
theorem discreteRecurrenceTime_le_ceil {d : ℕ} (α : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    discreteRecurrenceTime α r ≤ (⌈1 / r⌉₊ + 1) ^ d := by
  obtain ⟨n, hnpos, hnle, m, hm⟩ :=
    exists_fin_simultaneous_integer_approximation_quantitative (d := d) (Q := ⌈1 / r⌉₊) α
  have hstep : (1 : ℝ) / ((⌈1 / r⌉₊ : ℝ) + 1) ≤ r := by
    have hceil : (1 : ℝ) / r ≤ (⌈1 / r⌉₊ : ℝ) := Nat.le_ceil _
    have hpos : (0 : ℝ) < (⌈1 / r⌉₊ : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : (1 : ℝ) / r + 1 ≤ (⌈1 / r⌉₊ : ℝ) + 1 := by linarith
    have h2 : (1 : ℝ) ≤ r * ((1 : ℝ) / r + 1) := by
      field_simp
      linarith
    nlinarith [h1, h2, hr.le]
  have hmem : n ∈ {n : ℕ | 0 < n ∧ ∀ i, ∃ m : ℤ, |(n : ℝ) * α i - m| ≤ r} := by
    refine ⟨hnpos, fun i => ⟨m i, le_trans (hm i) ?_⟩⟩
    exact hstep
  exact le_trans (Nat.sInf_le hmem) hnle

/-- The real form of the same bound. -/
theorem discreteRecurrenceTime_le_pow {d : ℕ} (α : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    (discreteRecurrenceTime α r : ℝ) ≤ (1 / r + 2) ^ d := by
  have hceil : ((⌈1 / r⌉₊ : ℝ)) < 1 / r + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hbase : ((⌈1 / r⌉₊ : ℝ) + 1) ≤ 1 / r + 2 := by linarith
  have hnn : (0 : ℝ) ≤ (⌈1 / r⌉₊ : ℝ) + 1 := by positivity
  calc (discreteRecurrenceTime α r : ℝ) ≤ (((⌈1 / r⌉₊ + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast discreteRecurrenceTime_le_ceil α hr
    _ = ((⌈1 / r⌉₊ : ℝ) + 1) ^ d := by push_cast; ring
    _ ≤ (1 / r + 2) ^ d := pow_le_pow_left₀ hnn hbase d

/-- **The recurrence exponent is at most the number of phases.**  Logarithmic form of the Dirichlet
bound, valid for every spectrum. -/
theorem log_discreteRecurrenceTime_le {d : ℕ} (α : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    Real.log (discreteRecurrenceTime α r) ≤ (d : ℝ) * Real.log (1 / r + 2) := by
  rcases Nat.eq_zero_or_pos (discreteRecurrenceTime α r) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    have hlog : 0 ≤ Real.log (1 / r + 2) :=
      Real.log_nonneg (by nlinarith [one_div_pos.mpr hr])
    exact mul_nonneg (Nat.cast_nonneg d) hlog
  · have hposR : (0 : ℝ) < (discreteRecurrenceTime α r : ℝ) := by exact_mod_cast hpos
    have hle := discreteRecurrenceTime_le_pow α hr
    have hlog := Real.log_le_log hposR hle
    rwa [Real.log_pow] at hlog

/-- The comparison factor of the Dirichlet bound tends to one along `r = 1/N`. -/
theorem tendsto_dirichletShiftRatio :
    Tendsto (fun N : ℝ => Real.log (N + 2) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℝ => Real.log N) atTop atTop := Real.tendsto_log_atTop
  have hin : Tendsto (fun N : ℝ => 1 + 2 / N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at hin
  have hnum : Tendsto (fun N : ℝ => Real.log (1 + 2 / N)) atTop (𝓝 0) := by
    have hcont : ContinuousAt Real.log (1 : ℝ) :=
      Real.continuousAt_log (by norm_num)
    have h := hcont.tendsto.comp hin
    have hfun : (Real.log ∘ fun N : ℝ => 1 + 2 / N) = fun N : ℝ => Real.log (1 + 2 / N) := rfl
    rw [hfun] at h
    simpa using h
  have hzero : Tendsto (fun N : ℝ => Real.log (1 + 2 / N) / Real.log N) atTop (𝓝 0) :=
    hnum.div_atTop hlog
  have hone : Tendsto (fun N : ℝ => 1 + Real.log (1 + 2 / N) / Real.log N) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hzero
  rw [add_zero] at hone
  refine hone.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN
  have hlogpos : 0 < Real.log N := Real.log_pos hN
  have hsplit : Real.log (N + 2) = Real.log N + Real.log (1 + 2 / N) := by
    rw [← Real.log_mul (ne_of_gt hNpos) (by positivity)]
    congr 1
    field_simp
  rw [hsplit]
  field_simp

end RHTower
