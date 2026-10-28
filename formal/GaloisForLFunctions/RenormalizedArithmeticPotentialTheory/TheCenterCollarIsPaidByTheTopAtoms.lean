import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLogarithmicCenterRowCancelsThePole
import GaloisForLFunctions.HTGeometry.HarmonicCenterBoundaryBounds
import GaloisForLFunctions.HTGeometry.FiniteWeightedGroundStateBound

/-!
# The exact center collar is paid by the top-atom potential

Weighted Schur keeps the pole-gauge row potential `n(H_N+1)`. Dividing by the
horizon converts it to the top-atom potential `(n/N) log n`, up to an absolute
mass term. No maximum over the row index is taken.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry

/-- The complete center row has a linear pole-gauge potential. -/
theorem sum_archimedeanCenterKernel_div_sqrt_le {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j) ≤
      Real.sqrt n * ((harmonic N : ℝ) + 1) := by
  have hnN := (mem_Icc.mp hn).2
  have hlo : (harmonic (N - n) : ℝ) ≤ harmonic N := by
    have h := harmonic_add_sub_nonneg (N - n) n
    rw [Nat.sub_add_cancel hnN] at h
    linarith only [h]
  have hhi := harmonic_add_sub_le_one hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [sum_archimedeanCenterKernel_div_sqrt hn]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have ht : 0 ≤ 3 / (4 * (n : ℝ)) := by positivity
  linarith only [hlo, hhi, ht]

/-- The collar quadratic form is bounded by its exact weighted row potential. -/
theorem collar_quadratic_le_harmonic_diagonal (N : ℕ) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * archimedeanCenterKernel n j) ≤
      ∑ n ∈ Icc 1 N, (n : ℝ) * ((harmonic N : ℝ) + 1) * x n ^ 2 := by
  have hw (n : ℕ) (hn : n ∈ Icc 1 N) : 0 < 1 / Real.sqrt (n : ℝ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    exact one_div_pos.mpr (Real.sqrt_pos.mpr hn0)
  have h := finite_weighted_schur_row_potential (Icc 1 N) x
    (fun n => 1 / Real.sqrt n) archimedeanCenterKernel hw
    (fun n _ j _ => archimedeanCenterKernel_nonneg n j)
    (fun n _ j _ => archimedeanCenterKernel_comm n j)
  refine h.trans (sum_le_sum fun n hn => ?_)
  simp only [mul_one_div]
  have hrow := sum_archimedeanCenterKernel_div_sqrt_le hn
  have hmul := mul_le_mul_of_nonneg_left hrow
    (show 0 ≤ x n ^ 2 / (1 / Real.sqrt n) by positivity)
  calc
    _ ≤ x n ^ 2 / (1 / Real.sqrt n) * (Real.sqrt n * ((harmonic N : ℝ) + 1)) := hmul
    _ = _ := by
      simp only [div_eq_mul_inv, one_mul, inv_inv]
      rw [mul_assoc (x n ^ 2), ← mul_assoc (Real.sqrt (n : ℝ)),
        Real.mul_self_sqrt (Nat.cast_nonneg n)]
      ring

private theorem harmonic_top_diagonal_le {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (n : ℝ) / N * ((harmonic N : ℝ) + 1) ≤ (n : ℝ) / N * Real.log n + 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hN0 := hn0.trans_le hnN
  have hr : 0 ≤ (n : ℝ) / N := by positivity
  have hr1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hnN
  have hlog := Real.log_le_sub_one_of_pos (div_pos hN0 hn0)
  rw [Real.log_div hN0.ne' hn0.ne'] at hlog
  have hgap : (n : ℝ) / N * (Real.log N - Real.log n) ≤ 1 := by
    calc
      _ ≤ (n : ℝ) / N * ((N : ℝ) / n - 1) := mul_le_mul_of_nonneg_left hlog hr
      _ = 1 - (n : ℝ) / N := by field_simp [hn0.ne', hN0.ne']
      _ ≤ 1 := sub_le_self _ hr
  have hH := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) hr
  nlinarith only [hH, hgap, hr1]

/-- After division by the horizon, the exact collar costs the top potential plus three masses. -/
theorem collar_quadratic_div_horizon_le {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * archimedeanCenterKernel n j) / (N : ℝ) ≤
      (∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2) +
        3 * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (∑ n ∈ Icc 1 N, (n : ℝ) * ((harmonic N : ℝ) + 1) * x n ^ 2) / (N : ℝ) :=
      div_le_div_of_nonneg_right (collar_quadratic_le_harmonic_diagonal N x) hN0.le
    _ = ∑ n ∈ Icc 1 N, ((n : ℝ) / N * ((harmonic N : ℝ) + 1)) * x n ^ 2 := by
      rw [sum_div]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ ∑ n ∈ Icc 1 N, ((n : ℝ) / N * Real.log n + 3) * x n ^ 2 :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (harmonic_top_diagonal_le hn) (sq_nonneg _)
    _ = _ := by simp only [add_mul, sum_add_distrib, mul_sum]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
