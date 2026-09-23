import GaloisForLFunctions.HTGeometry.WeightedAverageRatioLimit
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The first logarithmic moment of a sequence with linear partial sums

For a non-negative sequence `c` with `c 0 = 0` whose partial sums `S(t) = Σ_{k ≤ t} c_k` satisfy
`S(t)/t → 1`,

`Σ_{k ≤ x} k log k · c_k / (x² log x) → 1/2`.

Abel summation gives `Σ_{k≤x} k log k c_k = x log x · S(x) − ∫_1^x (log t + 1) S(t) dt`; the
weighted average `∫ (log t+1) S / ∫ (log t+1) t` tends to `1`, and
`∫_1^x (log t + 1) t dt = ½ x² log x + ¼ x² − ¼`.

Applied to `c = Λ` (`S = ψ`) and to `c = log` on primes (`S = θ`), this evaluates
`Σ_{n ≤ x} Λ(n)² n ~ ½ x² log x`.
-/

open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The partial-sum function `S(t) = Σ_{k ≤ ⌊t⌋} c_k`. -/
noncomputable def partialSumReal (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k

theorem partialSumReal_mono {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) : Monotone (partialSumReal c) := by
  intro a b hab
  unfold partialSumReal
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_mono hab)) (fun k _ _ => hc k)

/-- A linear bound `S(t) ≤ C t` on `[1, ∞)` from `S(t)/t → 1`. -/
theorem exists_partialSumReal_le_mul {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    (hlim : Tendsto (fun t : ℝ => partialSumReal c t / t) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → partialSumReal c t ≤ C * t := by
  obtain ⟨u₀, hu₀⟩ := (Metric.tendsto_atTop.mp hlim) 1 one_pos
  set u₁ := max u₀ 1 with hu₁
  have hu₁1 : (1 : ℝ) ≤ u₁ := le_max_right _ _
  have hfar : ∀ t, u₁ ≤ t → partialSumReal c t ≤ 2 * t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos (hu₁1.trans ht)
    have h := hu₀ t ((le_max_left _ _).trans ht)
    rw [Real.dist_eq, abs_lt] at h
    have h2 : partialSumReal c t / t < 2 := by linarith [h.2]
    rw [div_lt_iff₀ ht0] at h2
    linarith
  refine ⟨2 * u₁, by positivity, fun t ht => ?_⟩
  rcases le_or_gt u₁ t with h | h
  · have := hfar t h
    nlinarith [hu₁1]
  · have h1 := partialSumReal_mono hc h.le
    have h2 := hfar u₁ le_rfl
    nlinarith [hu₁1]

/-! ## The weight `t (log t + 1)` -/

theorem hasDerivAt_mul_log {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
  have := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')
  refine this.congr_deriv ?_
  simp only [id_eq]
  field_simp

theorem hasDerivAt_halfSqLog {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s ^ (2 : ℕ) * Real.log s / 2 + s ^ (2 : ℕ) / 4) (t * (Real.log t + 1)) t := by
  have h1 := ((hasDerivAt_pow 2 t).mul (Real.hasDerivAt_log ht.ne')).div_const 2
  have h2 := (hasDerivAt_pow 2 t).div_const 4
  refine (h1.add h2).congr_deriv ?_
  simp only [Nat.cast_ofNat]
  field_simp
  ring

/-- `∫_1^x t (log t + 1) dt = ½ x² log x + ¼ x² − ¼`. -/
theorem integral_mul_log_add_one {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, t * (Real.log t + 1) = x ^ (2 : ℕ) * Real.log x / 2 + x ^ (2 : ℕ) / 4 - 1 / 4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_halfSqLog
    (by rw [uIcc_of_le hx] at ht; linarith [ht.1]))]
  · simp
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hx]
    refine continuousOn_id.mul ((Real.continuousOn_log.mono ?_).add continuousOn_const)
    intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]

theorem continuousOn_log_add_one : ContinuousOn (fun t : ℝ => Real.log t + 1) (Ici 1) := by
  refine (Real.continuousOn_log.mono ?_).add continuousOn_const
  intro t ht; simp only [mem_compl_iff, mem_singleton_iff, mem_Ici] at ht ⊢; linarith

theorem tendsto_integral_mul_log_add_one :
    Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, t * (Real.log t + 1)) atTop atTop := by
  have h : Tendsto (fun x : ℝ => x ^ (2 : ℕ) / 4 - 1 / 4) atTop atTop := by
    have := (tendsto_pow_atTop (two_ne_zero)).atTop_div_const (by norm_num : (0 : ℝ) < 4)
    exact tendsto_atTop_add_const_right _ _ this
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [integral_mul_log_add_one hx]
  have : 0 ≤ x ^ (2 : ℕ) * Real.log x / 2 := by
    have := Real.log_nonneg hx; positivity
  linarith

/-- `(½ x² log x + ¼ x² − ¼)/(x² log x) → 1/2`. -/
theorem tendsto_integral_mul_log_add_one_div :
    Tendsto (fun x : ℝ => (∫ t in (1 : ℝ)..x, t * (Real.log t + 1)) / (x ^ (2 : ℕ) * Real.log x))
      atTop (𝓝 (1 / 2)) := by
  have hlog : Tendsto (fun x : ℝ => (4 * Real.log x)⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).inv_tendsto_atTop
  have hsq : Tendsto (fun x : ℝ => (4 * (x ^ (2 : ℕ) * Real.log x))⁻¹) atTop (𝓝 0) :=
    (((tendsto_pow_atTop two_ne_zero).atTop_mul_atTop₀ Real.tendsto_log_atTop).const_mul_atTop
      (by norm_num : (0 : ℝ) < 4)).inv_tendsto_atTop
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add (hlog.sub hsq)
  simp only [sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [integral_mul_log_add_one (by linarith)]
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  field_simp
  ring

/-! ## The first logarithmic moment -/

/-- **`Σ_{k≤x} k log k · c_k / (x² log x) → 1/2`** when `S(t)/t → 1`. -/
theorem tendsto_sum_mul_log_div_sq_log {c : ℕ → ℝ} (hc0 : c 0 = 0) (hc : ∀ n, 0 ≤ c n)
    (hlim : Tendsto (fun t : ℝ => partialSumReal c t / t) atTop (𝓝 1)) :
    Tendsto (fun x : ℝ =>
      (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ((k : ℝ) * Real.log k) * c k) / (x ^ (2 : ℕ) * Real.log x))
      atTop (𝓝 (1 / 2)) := by
  -- Abel summation identity
  have habel : ∀ x : ℝ, 1 ≤ x →
      ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ((k : ℝ) * Real.log k) * c k
        = x * Real.log x * partialSumReal c x
          - ∫ t in (1 : ℝ)..x, partialSumReal c t * (Real.log t + 1) := by
    intro x hx
    have hderiv : ∀ t ∈ Icc (1 : ℝ) x, DifferentiableAt ℝ (fun s : ℝ => s * Real.log s) t :=
      fun t ht => (hasDerivAt_mul_log (by linarith [ht.1])).differentiableAt
    have hderiv_eq : EqOn (deriv fun s : ℝ => s * Real.log s) (fun t => Real.log t + 1) (Icc 1 x) :=
      fun t ht => (hasDerivAt_mul_log (by linarith [ht.1])).deriv
    have hint : IntegrableOn (deriv fun s : ℝ => s * Real.log s) (Icc 1 x) := by
      refine (continuousOn_log_add_one.mono Icc_subset_Ici_self).integrableOn_Icc.congr_fun
        (fun t ht => (hderiv_eq ht).symm) measurableSet_Icc
    have h := sum_mul_eq_sub_integral_mul₀ c hc0 x hderiv hint
    rw [partialSumReal, h, intervalIntegral.integral_of_le hx]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hderiv_eq ⟨ht.1.le, ht.2⟩, partialSumReal]
    ring
  -- the three limits
  have hS := partialSumReal_mono hc
  have hratio := tendsto_integral_mul_div_of_tendsto_div hS hlim continuousOn_log_add_one
    (fun t ht => by have := Real.log_nonneg ht; linarith) tendsto_integral_mul_log_add_one
  have hW := tendsto_integral_mul_log_add_one_div
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < ∫ t in (1 : ℝ)..x, t * (Real.log t + 1) :=
    tendsto_integral_mul_log_add_one.eventually_gt_atTop 0
  have h := hlim.sub (hratio.mul hW)
  rw [one_mul, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ), hpos] with x hx hWx
  rw [habel x (by linarith)]
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hx0 : 0 < x := by linarith
  field_simp

end RHTower
