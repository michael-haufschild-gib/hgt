import GaloisForLFunctions.RHTower.PNTFirstLogMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic tail moments of a sequence with linear partial sums

For a non-negative sequence `c` with `c 0 = 0` and partial sums `S(t) ~ t`, and every `k`,

`(x^{k+1} / log x) · Σ_{n > x} c_n log n / n^{k+2} → 1/(k+1)`.

Abel summation on `(x, ∞)` gives `Σ_{n>x} c_n f(n) = −f(x) S(x) + ∫_x^∞ S(t) w(t) dt` with
`f(t) = log t/t^{k+2}` and `w = −f'`; `S ~ t` turns the integral into
`∫_x^∞ ((k+2) log t − 1)/t^{k+2} dt = ((k+2) log x/(k+1) + 1/(k+1)²)/x^{k+1}`, and
`−1 + (k+2)/(k+1) = 1/(k+1)`.
-/

open MeasureTheory Filter Topology Set Asymptotics
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The tail weight `f(t) = log t / t^{k+2}`. -/
noncomputable def tailWeight (k : ℕ) (t : ℝ) : ℝ := Real.log t / t ^ (k + 2)

/-- Its derivative `(1 − (k+2) log t)/t^{k+3}`. -/
noncomputable def tailDeriv (k : ℕ) (t : ℝ) : ℝ := (1 - ((k : ℝ) + 2) * Real.log t) / t ^ (k + 3)

theorem hasDerivAt_tailWeight (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (tailWeight k) (tailDeriv k t) t := by
  have h := (Real.hasDerivAt_log ht.ne').div (hasDerivAt_pow (k + 2) t) (pow_ne_zero _ ht.ne')
  refine h.congr_deriv ?_
  unfold tailDeriv
  have hne : t ≠ 0 := ht.ne'
  field_simp
  push_cast
  ring

theorem deriv_tailWeight (k : ℕ) {t : ℝ} (ht : 0 < t) : deriv (tailWeight k) t = tailDeriv k t :=
  (hasDerivAt_tailWeight k ht).deriv

theorem continuousOn_tailDeriv (k : ℕ) : ContinuousOn (tailDeriv k) (Ici 1) := by
  unfold tailDeriv
  refine ContinuousOn.div (continuousOn_const.sub (continuousOn_const.mul ?_)) (by fun_prop)
    fun t ht => ?_
  · refine Real.continuousOn_log.mono fun t ht => ?_
    simp only [mem_compl_iff, mem_singleton_iff, mem_Ici] at ht ⊢; linarith
  · simp only [mem_Ici] at ht; positivity

theorem measurable_tailDeriv (k : ℕ) : Measurable (tailDeriv k) := by
  unfold tailDeriv
  exact (measurable_const.sub (measurable_const.mul Real.measurable_log)).div (measurable_id.pow_const _)

/-- `|1 − (k+2) log t| ≤ (k+2) log t + 1` for `t ≥ 1`. -/
theorem abs_one_sub_mul_log_le (k : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    |1 - ((k : ℝ) + 2) * Real.log t| ≤ ((k : ℝ) + 2) * Real.log t + 1 := by
  have := Real.log_nonneg ht
  rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- `log t ≤ 2 √t`, in `rpow` form. -/
theorem log_le_two_mul_rpow_half {t : ℝ} (ht : 0 ≤ t) : Real.log t ≤ 2 * t ^ ((1 / 2 : ℝ)) := by
  have := Real.log_le_rpow_div ht (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [div_eq_mul_inv, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num] at this
  linarith

/-- The tail primitive `G(t) = −((k+2) log t/(k+1) + 1/(k+1)²)/t^{k+1}`, with `G' = t · (−f')`. -/
noncomputable def tailPrimitive (k : ℕ) (t : ℝ) : ℝ :=
  -((((k : ℝ) + 2) * Real.log t) / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) ^ 2) / t ^ (k + 1)

theorem hasDerivAt_tailPrimitive (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (tailPrimitive k) ((((k : ℝ) + 2) * Real.log t - 1) / t ^ (k + 2)) t := by
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hA : HasDerivAt (fun s : ℝ => (((k : ℝ) + 2) * Real.log s) / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) ^ 2)
      ((((k : ℝ) + 2) * t⁻¹) / ((k : ℝ) + 1)) t := by
    have := (((Real.hasDerivAt_log ht.ne').const_mul ((k : ℝ) + 2)).div_const ((k : ℝ) + 1)).add_const
      (1 / ((k : ℝ) + 1) ^ 2)
    exact this
  have h := (hA.div (hasDerivAt_pow (k + 1) t) (pow_ne_zero _ ht.ne')).neg
  refine h.congr_deriv ?_
  have hne : t ≠ 0 := ht.ne'
  field_simp
  push_cast
  ring

theorem tendsto_log_div_pow_succ (k : ℕ) :
    Tendsto (fun t : ℝ => Real.log t / t ^ (k + 1)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact div_nonneg (Real.log_nonneg ht) (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    apply div_le_div_of_nonneg_left (Real.log_nonneg ht) ht0
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ (k + 1) := pow_le_pow_right₀ ht (by omega)

theorem tendsto_tailPrimitive (k : ℕ) : Tendsto (tailPrimitive k) atTop (𝓝 0) := by
  have h1 := (tendsto_log_div_pow_succ k).const_mul (((k : ℝ) + 2) / ((k : ℝ) + 1))
  have h2 : Tendsto (fun t : ℝ => (1 / ((k : ℝ) + 1) ^ 2) * (t ^ (k + 1))⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (Nat.succ_ne_zero k))).const_mul _
  have h := (h1.add h2).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold tailPrimitive
  field_simp

/-- `2 log 2 ≥ 1`. -/
theorem one_le_two_mul_log_two : (1 : ℝ) ≤ 2 * Real.log 2 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at this
  linarith

/-- `∫_x^∞ ((k+2) log t − 1)/t^{k+2} dt = ((k+2) log x/(k+1) + 1/(k+1)²)/x^{k+1}` for `x ≥ 2`,
with integrability. -/
theorem integral_Ioi_tailWeightMul (k : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t : ℝ => (((k : ℝ) + 2) * Real.log t - 1) / t ^ (k + 2)) (Ioi x) ∧
      ∫ t in Ioi x, (((k : ℝ) + 2) * Real.log t - 1) / t ^ (k + 2)
        = ((((k : ℝ) + 2) * Real.log x) / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) ^ 2) / x ^ (k + 1) := by
  have hcont : ContinuousWithinAt (tailPrimitive k) (Ici x) x :=
    (hasDerivAt_tailPrimitive k (by linarith)).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt (tailPrimitive k)
      ((((k : ℝ) + 2) * Real.log t - 1) / t ^ (k + 2)) t :=
    fun t ht => hasDerivAt_tailPrimitive k (by simp only [mem_Ioi] at ht; linarith)
  have hnonneg : ∀ t ∈ Ioi x, 0 ≤ (((k : ℝ) + 2) * Real.log t - 1) / t ^ (k + 2) := by
    intro t ht
    simp only [mem_Ioi] at ht
    have hlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
    have h1 := one_le_two_mul_log_two
    have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    apply div_nonneg _ (by positivity)
    nlinarith
  have htend := tendsto_tailPrimitive k
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg htend, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg htend]
  unfold tailPrimitive
  ring

/-! ## The tail moment -/

/-- **`(x^{k+1}/log x) Σ_{n>x} c_n log n / n^{k+2} → 1/(k+1)`** when `S(t)/t → 1`. -/
theorem tendsto_tail_log_moment {c : ℕ → ℝ} (hc0 : c 0 = 0) (hc : ∀ n, 0 ≤ c n)
    (hlim : Tendsto (fun t : ℝ => partialSumReal c t / t) atTop (𝓝 1)) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (k + 1) / Real.log x *
        ∑' n : ℕ, (if x < (n : ℝ) then c n * Real.log n / (n : ℝ) ^ (k + 2) else 0))
      atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
  obtain ⟨C, hC, hCle⟩ := exists_partialSumReal_le_mul hc hlim
  have hS := partialSumReal_mono hc
  have hS0 : ∀ t, 0 ≤ partialSumReal c t := fun t => Finset.sum_nonneg fun n _ => hc n
  -- differentiability and local integrability of the weight
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ (tailWeight k) t :=
    fun t ht => (hasDerivAt_tailWeight k (by simp only [mem_Ici] at ht; linarith)).differentiableAt
  have hderiv_eq : EqOn (deriv (tailWeight k)) (tailDeriv k) (Ici 1) :=
    fun t ht => deriv_tailWeight k (by simp only [mem_Ici] at ht; linarith)
  have hf_int : LocallyIntegrableOn (deriv (tailWeight k)) (Ici 1) :=
    ((continuousOn_tailDeriv k).congr hderiv_eq.symm).locallyIntegrableOn measurableSet_Ici
  -- the boundary term tends to zero
  have h_lim : Tendsto (fun n : ℕ => tailWeight k n * ∑ i ∈ Finset.Icc 0 n, c i) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, 1 ≤ n →
        tailWeight k n * ∑ i ∈ Finset.Icc 0 n, c i ≤ C * (Real.log n / n) := by
      intro n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hSn : ∑ i ∈ Finset.Icc 0 n, c i ≤ C * n := by
        have := hCle n hn'
        rwa [partialSumReal, Nat.floor_natCast] at this
      have hpos : 0 ≤ ∑ i ∈ Finset.Icc 0 n, c i := Finset.sum_nonneg fun i _ => hc i
      unfold tailWeight
      have hlog := Real.log_nonneg hn'
      calc Real.log n / (n : ℝ) ^ (k + 2) * ∑ i ∈ Finset.Icc 0 n, c i
          ≤ Real.log n / (n : ℝ) ^ (k + 2) * (C * n) :=
            mul_le_mul_of_nonneg_left hSn (by positivity)
        _ = C * (Real.log n / (n : ℝ) ^ (k + 1)) := by
            rw [pow_succ]; field_simp
        _ ≤ C * (Real.log n / n) := by
            gcongr
            calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
              _ ≤ (n : ℝ) ^ (k + 1) := pow_le_pow_right₀ hn' (by omega)
    have hlogn : Tendsto (fun n : ℕ => C * (Real.log n / n)) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
      simp only [pow_one, one_mul, add_zero, Function.comp] at h
      simpa using h.const_mul C
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlogn ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (div_nonneg (Real.log_nonneg hn') (by positivity))
        (Finset.sum_nonneg fun i _ => hc i)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact hbound n hn
  -- domination of `f' S` by `t^{-3/2}`
  have hg_dom : (fun t : ℝ => deriv (tailWeight k) t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i)
      =O[atTop] (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) := by
    refine IsBigO.of_bound (C * (2 * ((k : ℝ) + 2) + 1)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    rw [hderiv_eq (mem_Ici.mpr ht), Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hS0 t), abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    have hSt := hCle t ht
    unfold tailDeriv
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ (k + 3))]
    have hnum := abs_one_sub_mul_log_le k ht
    have hlog := log_le_two_mul_rpow_half ht0.le
    have hhalf : (1 : ℝ) ≤ t ^ ((1 / 2 : ℝ)) := Real.one_le_rpow ht (by norm_num)
    have hpow : t ^ 2 ≤ t ^ (k + 3) := pow_le_pow_right₀ ht (by omega)
    have hkey : |1 - ((k : ℝ) + 2) * Real.log t| * partialSumReal c t
        ≤ (2 * ((k : ℝ) + 2) + 1) * t ^ ((1 / 2 : ℝ)) * (C * t) := by
      have h1 : |1 - ((k : ℝ) + 2) * Real.log t| ≤ (2 * ((k : ℝ) + 2) + 1) * t ^ ((1 / 2 : ℝ)) := by
        refine hnum.trans ?_
        have hk : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
        nlinarith
      exact mul_le_mul h1 hSt (hS0 t) (by positivity)
    have hrpow : t ^ ((1 / 2 : ℝ)) * t / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
      rw [show t ^ 2 = t ^ (2 : ℝ) by norm_cast, show t = t ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add ht0, ← Real.rpow_sub ht0]
      norm_num
    calc |1 - ((k : ℝ) + 2) * Real.log t| / t ^ (k + 3) * partialSumReal c t
        = |1 - ((k : ℝ) + 2) * Real.log t| * partialSumReal c t / t ^ (k + 3) := by ring
      _ ≤ (2 * ((k : ℝ) + 2) + 1) * t ^ ((1 / 2 : ℝ)) * (C * t) / t ^ (k + 3) := by
          gcongr
      _ ≤ (2 * ((k : ℝ) + 2) + 1) * t ^ ((1 / 2 : ℝ)) * (C * t) / t ^ 2 := by
          gcongr
      _ = C * (2 * ((k : ℝ) + 2) + 1) * (t ^ ((1 / 2 : ℝ)) * t / t ^ 2) := by ring
      _ = C * (2 * ((k : ℝ) + 2) + 1) * t ^ (-(3 / 2 : ℝ)) := by rw [hrpow]
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-(3 / 2 : ℝ))) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos⟩
  -- the infinite Abel summation
  have hten := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc0 hf_diff hf_int h_lim hg_dom hg_int
  rw [zero_sub] at hten
  -- integrability of `f' S` on `(1, ∞)`
  have hFS : IntegrableOn (fun t : ℝ => deriv (tailWeight k) t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i)
      (Ici 1) :=
    (locallyIntegrableOn_mul_sum_Icc c zero_le_one hf_int).integrableOn_of_isBigO_atTop hg_dom hg_int
  -- summability of the series and identification of its sum
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ tailWeight k n * c n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg (div_nonneg (Real.log_nonneg hn') (by positivity)) (hc n)
  have hsum : Summable (fun n : ℕ => tailWeight k n * c n) := by
    obtain ⟨B, hB⟩ := hten.bddAbove_range
    refine summable_of_sum_range_le hterm_nonneg (c := B) fun n => ?_
    have h1 : ∑ i ∈ Finset.range n, tailWeight k i * c i ≤ ∑ i ∈ Finset.Icc 0 n, tailWeight k i * c i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hterm_nonneg i
      intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    exact h1.trans (hB ⟨n, rfl⟩)
  have htsum : ∑' n : ℕ, tailWeight k n * c n
      = -∫ t in Ioi 1, deriv (tailWeight k) t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i := by
    have h1 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc 0 n, tailWeight k i * c i) atTop
        (𝓝 (∑' n : ℕ, tailWeight k n * c n)) := by
      have := hsum.hasSum.tendsto_sum_nat
      have h2 := this.comp (Filter.tendsto_add_atTop_nat 1)
      refine h2.congr fun n => ?_
      simp only [Function.comp]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp only [Finset.mem_range, Finset.mem_Icc]; omega
    exact tendsto_nhds_unique h1 hten
  -- the tail identity for `x ≥ 2`
  have htail : ∀ x : ℝ, 2 ≤ x →
      ∑' n : ℕ, (if x < (n : ℝ) then c n * Real.log n / (n : ℝ) ^ (k + 2) else 0)
        = -(tailWeight k x * partialSumReal c x)
          + ∫ t in Ioi x, partialSumReal c t * (-tailDeriv k t) := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by linarith
    -- split the series at `x`
    have hsplit : ∑' n : ℕ, tailWeight k n * c n
        = (∑ i ∈ Finset.Icc 0 ⌊x⌋₊, tailWeight k i * c i)
          + ∑' n : ℕ, (if x < (n : ℝ) then c n * Real.log n / (n : ℝ) ^ (k + 2) else 0) := by
      have hle : Summable (fun n : ℕ => if (n : ℝ) ≤ x then tailWeight k n * c n else 0) :=
        Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hterm_nonneg n])
          (fun n => by split_ifs <;> simp [hterm_nonneg n]) hsum
      have hgt : Summable (fun n : ℕ => if x < (n : ℝ) then c n * Real.log n / (n : ℝ) ^ (k + 2)
          else 0) := by
        refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
        · split_ifs with h
          · exact div_nonneg (mul_nonneg (hc n) (Real.log_nonneg (by linarith))) (by positivity)
          · exact le_rfl
        · split_ifs with h
          · unfold tailWeight; ring_nf; exact le_rfl
          · exact hterm_nonneg n
      rw [← hle.tsum_add hgt]
      · congr 1
        · rw [tsum_eq_sum (s := Finset.Icc 0 ⌊x⌋₊) fun n hn => ?_]
          · refine Finset.sum_congr rfl fun n hn => ?_
            rw [if_pos]
            simp only [Finset.mem_Icc] at hn
            exact (Nat.le_floor_iff (by linarith)).mp hn.2
          · rw [if_neg]
            simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le] at hn
            intro hle'
            exact absurd (Nat.le_floor hle') (not_le.mpr hn)
        · refine tsum_congr fun n => ?_
          split_ifs with h1 h2
          · exact absurd h2 (not_lt.mpr h1)
          · rfl
          · rfl
          · exact absurd (le_of_not_gt h2) h1
    -- the finite Abel summation up to `x`
    have hfin := sum_mul_eq_sub_integral_mul₀ c hc0 x (fun t ht => hf_diff t (mem_Ici.mpr ht.1))
      (hFS.mono_set (Icc_subset_Ici_self) |>.integrableOn_of ?_)
    all_goals sorry
  sorry

end RHTower
