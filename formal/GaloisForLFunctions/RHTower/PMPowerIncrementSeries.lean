import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The positive series carried by power increments

Bernoulli concavity gives a telescoping majorant for the normalized increments
of `n^σ`. Their response series is also the exact sum of `n^σ/[n(n+1)]`, and
lies strictly above one and at most `1/(1-σ)` for `0<σ<1`. This supplies the
summable majorant needed to pass actual prime-weighted floor sums to their limit.
-/

open Filter Topology Finset
noncomputable section
namespace RHTower

def pmPowerIncrement (σ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ

def pmPowerIncrementKernel (σ : ℝ) (n : ℕ) : ℝ := pmPowerIncrement σ n / ((n : ℝ) + 1)

def pmPowerResponseKernel (σ : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ σ / (((n : ℝ) + 1) * ((n : ℝ) + 2))

def pmPowerResponse (σ : ℝ) : ℝ := ∑' n : ℕ, pmPowerIncrementKernel σ n

theorem pmPowerIncrement_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    0 ≤ pmPowerIncrement σ n :=
  sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) hσ)

theorem pmPowerIncrementKernel_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    0 ≤ pmPowerIncrementKernel σ n := div_nonneg (pmPowerIncrement_nonneg hσ n) (by positivity)

theorem pmPowerResponseKernel_nonneg (σ : ℝ) (n : ℕ) :
    0 ≤ pmPowerResponseKernel σ n := by unfold pmPowerResponseKernel; positivity

theorem rpow_add_one_le_tangent {σ x : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hx : 0 < x) :
    (x + 1) ^ σ ≤ x ^ σ + σ * (x ^ σ / x) := by
  have hb := rpow_one_add_le_one_add_mul_self (s := 1 / x) (by linarith [one_div_pos.mpr hx]) hσ0 hσ1
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le σ)
  rw [← Real.mul_rpow hx.le (by positivity : 0 ≤ 1 + 1 / x)] at hm
  have he : x * (1 + 1 / x) = x + 1 := by field_simp
  rw [he] at hm
  calc
    _ ≤ x ^ σ * (1 + σ * (1 / x)) := hm
    _ = _ := by ring

theorem pmPowerIncrementKernel_succ_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (n : ℕ) :
    pmPowerIncrementKernel σ (n + 1) ≤ σ / (1 - σ) *
      (((n : ℝ) + 1) ^ (σ - 1) - ((n : ℝ) + 2) ^ (σ - 1)) := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hy : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hb := div_le_div_of_nonneg_right (rpow_add_one_le_tangent hσ0 hσ1.le hx) hy.le
  have he : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [he] at hb
  have hc : ((n : ℝ) + 2) ^ σ / ((n : ℝ) + 2) ≤
      (1 - σ) * (((n : ℝ) + 1) ^ σ / ((n : ℝ) + 2)) +
        σ * (((n : ℝ) + 1) ^ σ / ((n : ℝ) + 1)) := by
    calc
      _ ≤ (((n : ℝ) + 1) ^ σ + σ * (((n : ℝ) + 1) ^ σ / ((n : ℝ) + 1))) /
          ((n : ℝ) + 2) := hb
      _ = _ := by field_simp; ring
  rw [pmPowerIncrementKernel, pmPowerIncrement, Nat.cast_add, Nat.cast_one, he,
    Real.rpow_sub_one hx.ne', Real.rpow_sub_one hy.ne', sub_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hσ1)).mpr
  nlinarith only [hc]

theorem sum_pmPowerIncrementKernel_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (N : ℕ) :
    (∑ n ∈ range N, pmPowerIncrementKernel σ n) ≤ 1 / (1 - σ) := by
  cases N with
  | zero => simpa using (one_div_nonneg.mpr (sub_pos.mpr hσ1).le)
  | succ N =>
    rw [sum_range_succ']
    have hzero : pmPowerIncrementKernel σ 0 = 1 := by
      simp [pmPowerIncrementKernel, pmPowerIncrement, Real.zero_rpow hσ0.ne']
    rw [hzero]
    have hb := sum_le_sum (fun n (_ : n ∈ range N) => pmPowerIncrementKernel_succ_le hσ0.le hσ1 n)
    rw [← mul_sum] at hb
    have he : (∑ n ∈ range N, (((n : ℝ) + 1) ^ (σ - 1) - ((n : ℝ) + 2) ^ (σ - 1))) =
        1 - ((N : ℝ) + 1) ^ (σ - 1) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, Real.one_rpow,
        show ∀ n : ℕ, (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by intro n; ring] using
          sum_range_sub' (fun n : ℕ => ((n : ℝ) + 1) ^ (σ - 1)) N
    rw [he] at hb
    have hp := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1) (σ - 1)
    have hc : 1 + σ / (1 - σ) = 1 / (1 - σ) := by
      field_simp [(sub_pos.mpr hσ1).ne']
      ring
    rw [← hc]
    have hcoeff : 0 ≤ σ / (1 - σ) := div_nonneg hσ0.le (sub_pos.mpr hσ1).le
    nlinarith

theorem summable_pmPowerIncrementKernel {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Summable (pmPowerIncrementKernel σ) :=
  summable_of_sum_range_le (pmPowerIncrementKernel_nonneg hσ0.le)
    (sum_pmPowerIncrementKernel_le hσ0 hσ1)

theorem pmPowerResponse_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    pmPowerResponse σ ≤ 1 / (1 - σ) :=
  Real.tsum_le_of_sum_range_le (pmPowerIncrementKernel_nonneg hσ0.le)
    (sum_pmPowerIncrementKernel_le hσ0 hσ1)

theorem sum_pmPowerIncrementKernel_eq {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    (∑ n ∈ range N, pmPowerIncrementKernel σ n) =
      (∑ n ∈ range N, pmPowerResponseKernel σ n) + (N : ℝ) ^ σ / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [Real.zero_rpow hσ.ne']
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih, pmPowerIncrementKernel, pmPowerIncrement,
      pmPowerResponseKernel]
    push_cast
    field_simp
    ring

theorem summable_pmPowerResponseKernel {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Summable (pmPowerResponseKernel σ) := by
  apply summable_of_sum_range_le (pmPowerResponseKernel_nonneg σ) (c := 1 / (1 - σ))
  intro N
  have hb := sum_pmPowerIncrementKernel_le hσ0 hσ1 N
  rw [sum_pmPowerIncrementKernel_eq hσ0 N] at hb
  have hp : 0 ≤ (N : ℝ) ^ σ / ((N : ℝ) + 1) := by positivity
  linarith

theorem tendsto_pmPowerResponse_boundary {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ σ / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (σ - 1)) atTop (𝓝 0) := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_mono (show ∀ N : ℕ, (N : ℝ) ≤ (N : ℝ) + 1 from fun _ => by linarith)
      exact tendsto_natCast_atTop_atTop
    simpa only [neg_sub, Function.comp_def] using (tendsto_rpow_neg_atTop (sub_pos.mpr hσ1)).comp ht
  apply squeeze_zero (fun N => by positivity) (fun N => ?_) hp
  rw [Real.rpow_sub_one (by positivity : (N : ℝ) + 1 ≠ 0)]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) hσ0) (by positivity)

theorem pmPowerResponse_eq_tsum_kernel {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    pmPowerResponse σ = ∑' n : ℕ, pmPowerResponseKernel σ n := by
  have hl := (summable_pmPowerIncrementKernel hσ0 hσ1).hasSum.tendsto_sum_nat
  have hr := (summable_pmPowerResponseKernel hσ0 hσ1).hasSum.tendsto_sum_nat.add
    (tendsto_pmPowerResponse_boundary hσ0.le hσ1)
  simp only [add_zero] at hr
  apply tendsto_nhds_unique hl
  exact hr.congr (fun N => (sum_pmPowerIncrementKernel_eq hσ0 N).symm)


theorem one_lt_pmPowerResponse {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    1 < pmPowerResponse σ := by
  have hl := (summable_pmPowerIncrementKernel hσ0 hσ1).sum_le_tsum
    (range 2) (fun n _ => pmPowerIncrementKernel_nonneg hσ0.le n)
  have hp : 0 < pmPowerIncrementKernel σ 1 := by
    have hr := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2) hσ0
    rw [Real.one_rpow] at hr
    norm_num only [pmPowerIncrementKernel, pmPowerIncrement, Nat.cast_one, Real.one_rpow]
    exact div_pos (sub_pos.mpr hr) (by norm_num)
  have hzero : pmPowerIncrementKernel σ 0 = 1 := by
    simp [pmPowerIncrementKernel, pmPowerIncrement, Real.zero_rpow hσ0.ne']
  have hlow : 1 + pmPowerIncrementKernel σ 1 ≤ pmPowerResponse σ := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, sum_range_succ, sum_range_zero, zero_add, hzero,
      pmPowerResponse] using hl
  exact (lt_add_of_pos_right 1 hp).trans_le hlow

end RHTower
