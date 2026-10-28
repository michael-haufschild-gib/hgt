import GaloisForLFunctions.HTGeometry.FinitePoleWeightedDistanceRows
import GaloisForLFunctions.HTGeometry.FiniteWeightedGroundStateBound

/-!
# Finite kernel errors controlled by integer distances

A reciprocal-square majorant gives a uniform quadratic-form bound. Its finer
pole-weighted row estimate also controls the Euclidean square residual of every
bounded pole profile. Both estimates retain the horizon dependence explicitly.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {N : ℕ} {E : ℕ → ℕ → ℝ} {K : ℝ}

/-- Integer-square entry control gives an absolute row bound. -/
theorem sum_abs_kernel_le_of_integer_distance (hK : 0 ≤ K)
    (hE : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |E n j| ≤ K * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2)
    {n : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, |E n j|) ≤ 4 * K * (N : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Icc 1 N, K * (N : ℝ) ^ 2 / |(n : ℝ) - j| ^ 2 := by
      refine sum_le_sum fun j hj => (hE n hn j hj).trans ?_
      have hm : max (n : ℝ) j ≤ N :=
        max_le (by exact_mod_cast (mem_Icc.mp hn).2) (by exact_mod_cast (mem_Icc.mp hj).2)
      have hm0 : 0 ≤ max (n : ℝ) j := (Nat.cast_nonneg n).trans (le_max_left _ _)
      have hsq : (max (n : ℝ) j) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hm) (add_nonneg (Nat.cast_nonneg N) hm0)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK) (sq_nonneg _)
    _ = (K * (N : ℝ) ^ 2) * ∑ j ∈ Icc 1 N, 1 / |(n : ℝ) - j| ^ 2 := by
      simp only [mul_sum, mul_one_div]
    _ ≤ (K * (N : ℝ) ^ 2) * 4 :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_integer_distance_le_four _ n) (by positivity)
    _ = _ := by ring

/-- The same majorant has a sharper action on every bounded pole profile. -/
theorem abs_sum_kernel_poleProfile_le (hK : 0 ≤ K)
    (hE : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |E n j| ≤ K * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2)
    {a : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A)
    {n : ℕ} (hn : n ∈ Icc 1 N) :
    |∑ j ∈ Icc 1 N, E n j * (a j / Real.sqrt j)| ≤
      36 * K * A * (N : ℝ) * Real.sqrt n := by
  calc
    _ ≤ ∑ j ∈ Icc 1 N,
        (K * A) * ((max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hb : |a j| / Real.sqrt j ≤ A / Real.sqrt j :=
        div_le_div_of_nonneg_right (ha j hj) (Real.sqrt_nonneg _)
      have h := mul_le_mul (hE n hn j hj) hb (by positivity) (by positivity)
      convert h using 1
      ring
    _ = (K * A) * ∑ j ∈ Icc 1 N,
        (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) := (mul_sum ..).symm
    _ ≤ (K * A) * (36 * (N : ℝ) * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (sum_pole_weighted_distance_row_le hn) (mul_nonneg hK hA)
    _ = _ := by ring

/-- The square residual on a bounded pole profile grows at most as the fourth horizon power. -/
theorem sum_sq_kernel_poleProfile_le (hK : 0 ≤ K)
    (hE : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |E n j| ≤ K * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2)
    {a : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, E n j * (a j / Real.sqrt j)) ^ 2) ≤
      (36 * K * A) ^ 2 * (N : ℝ) ^ 4 := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ j ∈ Icc 1 N, E n j * (a j / Real.sqrt j)) ^ 2 ≤
        (36 * K * A * (N : ℝ)) ^ 2 * (n : ℝ) := by
    have h := abs_sum_kernel_poleProfile_le hK hE hA ha hn
    have hs : (∑ j ∈ Icc 1 N, E n j * (a j / Real.sqrt j)) ^ 2 ≤
        (36 * K * A * (N : ℝ) * Real.sqrt n) ^ 2 := by
      simpa only [← pow_two, sq_abs] using
        mul_self_le_mul_self (abs_nonneg (∑ j ∈ Icc 1 N, E n j * (a j / Real.sqrt j))) h
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using hs
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, (36 * K * A * (N : ℝ)) ^ 2 * (N : ℝ) := by
      refine sum_le_sum fun n hn => (hterm n hn).trans ?_
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hn).2) (sq_nonneg _)
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- A symmetric distance-controlled error costs only its row bound in a quadratic form. -/
theorem abs_kernel_quadratic_le_of_integer_distance (hK : 0 ≤ K)
    (hE : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |E n j| ≤ K * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2)
    (hsym : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, E n j = E j n) (x : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * E n j| ≤
      (4 * K * (N : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hschur := finite_weighted_schur_row_potential (Icc 1 N) (fun n => |x n|)
    (fun _ => (1 : ℝ)) (fun n j => |E n j|) (fun _ _ => zero_lt_one)
    (fun n _ j _ => abs_nonneg (E n j))
    (fun n hn j hj => congrArg abs (hsym n hn j hj))
  simp only [div_one, mul_one, sq_abs] at hschur
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |x n| * |x j| * |E n j| := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
      simpa only [abs_mul] using abs_sum_le_sum_abs (fun j => x n * x j * E n j) (Icc 1 N)
    _ ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * ∑ j ∈ Icc 1 N, |E n j| := hschur
    _ ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * (4 * K * (N : ℝ) ^ 2) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
        (sum_abs_kernel_le_of_integer_distance hK hE hn) (sq_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

end GaloisForLFunctions.HTGeometry
