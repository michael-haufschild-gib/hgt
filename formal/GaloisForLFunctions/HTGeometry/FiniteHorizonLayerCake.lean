import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Logarithmic integration of finite horizons

A pair enters every truncation after its larger index. Summing those
truncations against logarithmic increments recovers its distance to the
terminal horizon. The linear profile has asymptotic mass one.
-/

noncomputable section
open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A pair is present at every horizon beyond the larger of its two indices. -/
theorem sum_pair_horizon_layers (a : ℕ → ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, a i j * (f N - f (max i j))) =
      ∑ T ∈ Ico 1 N, (∑ i ∈ Icc 1 T, ∑ j ∈ Icc 1 T, a i j) * (f (T + 1) - f T) := by
  induction N with
  | zero => simp
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      simp
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have htop : (∑ j ∈ Icc 1 (N + 1), a (N + 1) j *
        (f (N + 1) - f (max (N + 1) j))) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [max_eq_left (mem_Icc.mp hj).2, sub_self, mul_zero]
    rw [sum_Icc_succ_top (by omega), htop, add_zero]
    have hrow : ∀ i ∈ Icc 1 N,
        (∑ j ∈ Icc 1 (N + 1), a i j * (f (N + 1) - f (max i j))) =
          ∑ j ∈ Icc 1 N, a i j * (f (N + 1) - f (max i j)) := by
      intro i hi
      rw [sum_Icc_succ_top (by omega), max_eq_right ((mem_Icc.mp hi).2.trans (Nat.le_succ N)),
        sub_self, mul_zero, add_zero]
    rw [sum_congr rfl hrow, sum_Ico_succ_top hN1, ← ih]
    rw [sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring

/-- The logarithmic distance to the top is an exact sum of nested horizon forms. -/
theorem sum_pair_log_max_eq_horizon_layers (a : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      a i j * (Real.log N - Real.log (max i j))) =
      ∑ T ∈ Ico 1 N, (∑ i ∈ Icc 1 T, ∑ j ∈ Icc 1 T, a i j) *
        (Real.log ((T : ℝ) + 1) - Real.log T) := by
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_max] using
    sum_pair_horizon_layers a (fun n => Real.log n) N

/-- A logarithmic horizon increment lies between its adjacent reciprocal weights. -/
theorem log_horizon_increment_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n ∧
      Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hup := Real.log_le_sub_one_of_pos (div_pos hn1 hn0)
  have hlo := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
  rw [Real.log_div hn1.ne' hn0.ne'] at hup
  rw [Real.log_div hn0.ne' hn1.ne'] at hlo
  have hu : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp [hn0.ne']; ring
  have hl : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1)) := by field_simp; ring
  rw [hu] at hup
  rw [hl] at hlo
  exact ⟨by linarith only [hlo], hup⟩

/-- The linear profile has unit total mass under logarithmic horizon integration. -/
theorem tendsto_linear_log_horizon_mass :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ T ∈ Ico 1 N, (T : ℝ) * (Real.log ((T : ℝ) + 1) - Real.log T)) atTop (𝓝 1) := by
  let w : ℕ → ℝ := fun n => (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n)
  have hbound : ∀ n : ℕ, 1 ≤ n → 0 ≤ 1 - w n ∧ 1 - w n ≤ 1 / ((n : ℝ) + 1) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨hlo, hup⟩ := log_horizon_increment_bounds hn
    have hu := mul_le_mul_of_nonneg_left hup hn0.le
    have hl := mul_le_mul_of_nonneg_left hlo hn0.le
    have hcancel : (n : ℝ) * (1 / n) = 1 := by field_simp [hn0.ne']
    have hadd : (n : ℝ) * (1 / (n + 1)) = 1 - 1 / (n + 1) := by field_simp; ring
    rw [hcancel] at hu
    rw [hadd] at hl
    dsimp only [w]
    exact ⟨by linarith only [hu], by linarith only [hl]⟩
  have hz : Tendsto (fun n : ℕ => 1 - w n) atTop (𝓝 0) :=
    squeeze_zero'
      ((eventually_ge_atTop 1).mono fun n hn => (hbound n hn).1)
      ((eventually_ge_atTop 1).mono fun n hn => (hbound n hn).2)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Tendsto w atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
    simpa only [sub_zero, sub_sub_cancel] using h
  apply hw.cesaro.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_range_eq_add_Ico w (by omega : 0 < N)]
  simp only [w, Nat.cast_zero, zero_mul, zero_add]


/-- A bounded prefix contributes only its cardinality to an otherwise small row sum. -/
theorem abs_sum_range_le_of_prefix_bounds (f : ℕ → ℝ) (N M : ℕ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hhead : ∀ n < N, n < M → |f n| ≤ C)
    (htail : ∀ n < N, M ≤ n → |f n| ≤ D) :
    |∑ n ∈ range N, f n| ≤ C * M + D * N := by
  have hpoint : ∀ n ∈ range N, |f n| ≤ (if n < M then C else 0) + D := by
    intro n hn
    by_cases hnm : n < M
    · rw [if_pos hnm]
      exact (hhead n (mem_range.mp hn) hnm).trans (le_add_of_nonneg_right hD)
    · rw [if_neg hnm, zero_add]
      exact htail n (mem_range.mp hn) (Nat.le_of_not_gt hnm)
  have hcard : ((range N).filter (fun n => n < M)).card ≤ M := by
    have hsub : (range N).filter (fun n => n < M) ⊆ range M :=
      fun n hn => mem_range.mpr (mem_filter.mp hn).2
    simpa only [card_range] using card_le_card hsub
  calc
    _ ≤ ∑ n ∈ range N, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range N, ((if n < M then C else 0) + D) := sum_le_sum hpoint
    _ = (((range N).filter (fun n => n < M)).card : ℝ) * C + (N : ℝ) * D := by
      rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_range, nsmul_eq_mul,
        nsmul_eq_mul]
    _ ≤ C * M + D * N := by
      have hc : (((range N).filter (fun n => n < M)).card : ℝ) ≤ M := by exact_mod_cast hcard
      have h := mul_le_mul_of_nonneg_right hc hC
      nlinarith only [h]

/-- Uniformly small tails determine a mean when the exceptional prefixes have zero density. -/
theorem tendsto_triangular_mean_zero_of_sparse_prefixes
    (f : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ n < N, |f N n| ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ → ℕ,
      Tendsto (fun N : ℕ => (M N : ℝ) / N) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ n < N, M N ≤ n → |f N n| ≤ ε) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, f N n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨M, hM, htailM⟩ := htail (ε / 2) (by positivity)
  have hsmall : ∀ᶠ N : ℕ in atTop, C * ((M N : ℝ) / N) < ε / 2 := by
    have hlim := hM.const_mul C
    simp only [mul_zero] at hlim
    exact hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hbound, htailM, hsmall, eventually_ge_atTop 1] with N hb ht hs hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dist_zero_right, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hN0.le)]
  calc
    _ ≤ (N : ℝ)⁻¹ * (C * M N + (ε / 2) * N) :=
      mul_le_mul_of_nonneg_left
        (abs_sum_range_le_of_prefix_bounds (f N) N (M N) hC (by positivity)
          (fun n hn _ => hb n hn) ht)
        (inv_nonneg.mpr hN0.le)
    _ = C * ((M N : ℝ) / N) + ε / 2 := by field_simp [hN0.ne']
    _ < ε := by linarith only [hs]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.sum_pair_log_max_eq_horizon_layers
#print axioms GaloisForLFunctions.HTGeometry.tendsto_linear_log_horizon_mass

#print axioms GaloisForLFunctions.HTGeometry.tendsto_triangular_mean_zero_of_sparse_prefixes
