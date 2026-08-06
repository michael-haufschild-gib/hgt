import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# Mertens' second theorem in the real variable

The prime reciprocal sum evaluated at `⌊t⌋` satisfies

```text
∑_{p ≤ t} 1/p - log log t → M      (t → ∞),
```

because the floor changes `log log` by at most `2 / (t log ⌊t⌋)`.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem log_sub_log_floor_le {t : ℝ} (ht : 2 ≤ t) :
    Real.log t - Real.log ⌊t⌋₊ ≤ 2 / t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
  have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
  have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have hlt : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hhalf : t ≤ 2 * ((⌊t⌋₊ : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor1
    linarith
  have hratio : (0 : ℝ) < t / ((⌊t⌋₊ : ℕ) : ℝ) := div_pos ht0 hfloorpos
  have h := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div ht0.ne' hfloorpos.ne'] at h
  have hstep : t / ((⌊t⌋₊ : ℕ) : ℝ) - 1 ≤ 2 / t := by
    rw [div_sub_one hfloorpos.ne', div_le_div_iff₀ hfloorpos ht0]
    nlinarith
  linarith

private theorem tendsto_logFloor_sub_log_zero :
    Tendsto (fun t : ℝ => Real.log (Real.log ⌊t⌋₊) - Real.log (Real.log t)) atTop (nhds 0) := by
  have hb : ∀ᶠ t : ℝ in atTop,
      ‖Real.log (Real.log ⌊t⌋₊) - Real.log (Real.log t)‖ ≤ 2 / (t * Real.log 2) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hfloor2 : 2 ≤ ⌊t⌋₊ := by
      have : (2 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (2 : ℝ) ≤ t))
      exact this
    have hfloorr : (2 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor2
    have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hlogfloor : Real.log 2 ≤ Real.log ⌊t⌋₊ := Real.log_le_log (by norm_num) hfloorr
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogfloorpos : 0 < Real.log ⌊t⌋₊ := lt_of_lt_of_le hlog2 hlogfloor
    have hlogle : Real.log ⌊t⌋₊ ≤ Real.log t :=
      Real.log_le_log (by linarith) hfloorle
    have hgap := log_sub_log_floor_le (by linarith : (2 : ℝ) ≤ t)
    have hupper : Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ≤ 2 / (t * Real.log 2) := by
      have hratio : (0 : ℝ) < Real.log t / Real.log ⌊t⌋₊ :=
        div_pos (lt_of_lt_of_le hlogfloorpos hlogle) hlogfloorpos
      have h := Real.log_le_sub_one_of_pos hratio
      rw [Real.log_div (lt_of_lt_of_le hlogfloorpos hlogle).ne' hlogfloorpos.ne'] at h
      have hstep : Real.log t / Real.log ⌊t⌋₊ - 1 ≤ 2 / (t * Real.log 2) := by
        rw [div_sub_one hlogfloorpos.ne', div_le_div_iff₀ hlogfloorpos (by positivity)]
        have hkey : (Real.log t - Real.log ⌊t⌋₊) * (t * Real.log 2) ≤
            (2 / t) * (t * Real.log 2) :=
          mul_le_mul_of_nonneg_right hgap (by positivity)
        have hcancel : (2 / t) * (t * Real.log 2) = 2 * Real.log 2 := by
          field_simp
        rw [hcancel] at hkey
        linarith
      linarith
    have hlower : 0 ≤ Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) := by
      have := Real.log_le_log hlogfloorpos hlogle
      linarith
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  refine squeeze_zero_norm' hb ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : Tendsto (fun t : ℝ => t * Real.log 2) atTop atTop :=
    tendsto_id.atTop_mul_const hlog2
  exact Tendsto.div_atTop tendsto_const_nhds h

/-- **Mertens' second theorem in the real variable.** -/
theorem tendsto_primeRecipSum_floor_sub_logLog :
    Tendsto (fun t : ℝ => primeRecipSum ⌊t⌋₊ - Real.log (Real.log t)) atTop
      (nhds mertensSecondConstant) := by
  have hfloor : Tendsto (fun t : ℝ => (⌊t⌋₊ : ℕ)) atTop atTop := tendsto_nat_floor_atTop
  have h1 : Tendsto (fun t : ℝ => primeRecipSum ⌊t⌋₊ - Real.log (Real.log ⌊t⌋₊)) atTop
      (nhds mertensSecondConstant) := tendsto_primeRecipSum_sub_logLog.comp hfloor
  have h2 := h1.add tendsto_logFloor_sub_log_zero
  rw [add_zero] at h2
  refine h2.congr fun t => ?_
  ring

end

end RHTower
