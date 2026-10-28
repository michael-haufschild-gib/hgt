import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLogarithmicCenterKernelIsHarmonic
import GaloisForLFunctions.HTGeometry.FiniteShiftedHarmonicAbelBounds

/-!
# Bounded center rows on sequences with bounded interval sums

The pole-gauged center kernel is the half-sum of difference and sum reciprocal
kernels. Finite Abel bounds control both. Adding the two pole outer products
preserves a square-root row bound, hence a bounded square residual after division
by the horizon.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry

private theorem interval_bound_nonneg {a : ℕ → ℝ} {B : ℝ}
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) : 0 ≤ B := by
  simpa only [Ico_self, sum_empty, abs_zero] using hB 0 0 le_rfl

/-- Deleting the diagonal from a reciprocal-sum row costs at most one point value. -/
theorem abs_sum_erase_div_add_le {a : ℕ → ℝ} {A B : ℝ} {n N : ℕ}
    (hn : n ∈ Icc 1 N) (hA : 0 ≤ A) (ha : |a n| ≤ A)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ (Icc 1 N).erase n, a j / ((n : ℝ) + j)| ≤ B + A := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  have hB0 := interval_bound_nonneg hB
  have h := abs_sum_Ico_div_add_le (r := (n : ℝ)) hB 1 (N + 1) (by positivity)
  rw [Ico_add_one_right_eq_Icc] at h
  have hb : |∑ j ∈ Icc 1 N, a j / ((n : ℝ) + j)| ≤ B :=
    h.trans (by apply div_le_self hB0; push_cast; linarith only [hn1])
  have hd : |a n / ((n : ℝ) + n)| ≤ A := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (n : ℝ) + n by linarith only [hn1])]
    exact (div_le_div_of_nonneg_right ha (by positivity)).trans
      (div_le_self hA (by linarith only [hn1]))
  have heq := sum_erase_add (Icc 1 N) (fun j => a j / ((n : ℝ) + j)) hn
  have heq' : (∑ j ∈ (Icc 1 N).erase n, a j / ((n : ℝ) + j)) =
      (∑ j ∈ Icc 1 N, a j / ((n : ℝ) + j)) - a n / ((n : ℝ) + n) := by
    linarith only [heq]
  rw [heq']
  exact (abs_sub _ _).trans (add_le_add hb hd)

/-- The exact center collar has a uniform square-root row bound in pole gauge. -/
theorem abs_sum_archimedeanCenterKernel_poleProfile_le {a : ℕ → ℝ} {A B : ℝ} {n N : ℕ}
    (hn : n ∈ Icc 1 N) (hA : 0 ≤ A) (ha : |a n| ≤ A)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a j / Real.sqrt j)| ≤
      (2 * B + A) * Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn := (Real.sqrt_pos.mpr hn0).ne'
  have hB0 := interval_bound_nonneg hB
  have heq : (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a j / Real.sqrt j)) =
      Real.sqrt n / 2 * ((∑ j ∈ (Icc 1 N).erase n, a j / |(n : ℝ) - j|) +
        ∑ j ∈ (Icc 1 N).erase n, a j / ((n : ℝ) + j)) := by
    rw [← sum_erase_add (Icc 1 N) (fun j => archimedeanCenterKernel n j * (a j / Real.sqrt j)) hn,
      archimedeanCenterKernel_self, zero_mul, add_zero, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_erase.mp hj
    have h := archimedeanCenterKernel_div_sqrt_mul (mem_Icc.mp hn).1
      (mem_Icc.mp hj'.2).1 (Ne.symm hj'.1)
    calc
      archimedeanCenterKernel n j * (a j / Real.sqrt j) =
          Real.sqrt n * a j * (archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)) := by
        field_simp [hsn]
      _ = _ := by rw [h]; ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) / 2)]
  calc
    _ ≤ Real.sqrt n / 2 * (2 * B + (B + A)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (abs_add_le _ _).trans (add_le_add
        (abs_sum_erase_div_abs_sub_le hn hB) (abs_sum_erase_div_add_le hn hA ha hB))
    _ ≤ (2 * B + A) * Real.sqrt n := by
      have h := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (add_nonneg hB0 hA)
      nlinarith only [h]

/-- The two pole outer products obey the same square-root row scale. -/
theorem abs_sum_poleRows_poleProfile_le {a : ℕ → ℝ} {B : ℝ} {n N : ℕ}
    (hn : n ∈ Icc 1 N)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
        (a j / Real.sqrt j)| ≤ 2 * B * Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by linarith only [hn1]
  have hB0 := interval_bound_nonneg hB
  have heq : (∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * (a j / Real.sqrt j)) =
      Real.sqrt n * (∑ j ∈ Icc 1 N, a j / j) +
        (∑ j ∈ Icc 1 N, a j) / Real.sqrt n := by
    rw [mul_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hsj := (Real.sqrt_pos.mpr hj0).ne'
    calc
      _ = (Real.sqrt n * a j) / (Real.sqrt j * Real.sqrt j) +
          (Real.sqrt j / Real.sqrt j) * (a j / Real.sqrt n) := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt hj0.le, div_self hsj, one_mul]
        ring
  have hsum : |∑ j ∈ Icc 1 N, a j| ≤ B := by
    simpa only [Ico_add_one_right_eq_Icc] using hB 1 (N + 1) (by omega)
  have hinv : |∑ j ∈ Icc 1 N, a j / j| ≤ B := by
    simpa only [Ico_add_one_right_eq_Icc, zero_add, Nat.cast_one, div_one] using
      abs_sum_Ico_div_add_le (r := 0) hB 1 (N + 1) (by norm_num)
  have hrec : 1 / Real.sqrt (n : ℝ) ≤ Real.sqrt n := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hn0), ← sq, Real.sq_sqrt hn0.le]
    exact hn1
  rw [heq]
  calc
    _ ≤ Real.sqrt n * |∑ j ∈ Icc 1 N, a j / j| +
        |∑ j ∈ Icc 1 N, a j| / Real.sqrt n := by
      simpa only [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
        using abs_add_le (Real.sqrt n * (∑ j ∈ Icc 1 N, a j / j))
          ((∑ j ∈ Icc 1 N, a j) / Real.sqrt n)
    _ ≤ Real.sqrt n * B + B / Real.sqrt n := add_le_add
      (mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _))
      (div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg _))
    _ ≤ 2 * B * Real.sqrt n := by
      have h := mul_le_mul_of_nonneg_left hrec hB0
      rw [mul_one_div] at h
      linarith only [h]

/-- Restoring both poles leaves a uniformly bounded row on every mean-zero periodic profile. -/
theorem abs_sum_poleMinusCollar_poleProfile_le {a : ℕ → ℝ} {A B : ℝ} {n N : ℕ}
    (hn : n ∈ Icc 1 N) (hA : 0 ≤ A) (ha : |a n| ≤ A)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B) :
    |∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j) *
        (a j / Real.sqrt j)| ≤ (4 * B + A) * Real.sqrt n := by
  simp only [sub_mul, sum_sub_distrib]
  exact (abs_sub _ _).trans (by
    have hp := abs_sum_poleRows_poleProfile_le hn hB
    have hc := abs_sum_archimedeanCenterKernel_poleProfile_le hn hA ha hB
    linarith only [hp, hc])

/-- Division by the horizon makes the complete center correction uniformly square bounded. -/
theorem sum_sq_centerCorrection_poleProfile_le {a : ℕ → ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n, |a n| ≤ A)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a j| ≤ B)
    (α : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((α / N) * ∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j) *
        (a j / Real.sqrt j)) ^ 2) ≤ α ^ 2 * (4 * B + A) ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty]
    positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB0 := interval_bound_nonneg hB
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      ((α / N) * ∑ j ∈ Icc 1 N,
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j) *
          (a j / Real.sqrt j)) ^ 2 ≤
        (α / N) ^ 2 * (4 * B + A) ^ 2 * (N : ℝ) := by
    have h := abs_sum_poleMinusCollar_poleProfile_le hn hA (ha n) hB
    have hsq := mul_self_le_mul_self (abs_nonneg _) h
    rw [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
    rw [mul_pow]
    calc
      _ ≤ (α / N) ^ 2 * ((4 * B + A) ^ 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ ≤ _ := by
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg (α / N)) (sq_nonneg (4 * B + A)))
          (sub_nonneg.mpr hnN)]
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, (α / N) ^ 2 * (4 * B + A) ^ 2 * (N : ℝ) :=
      sum_le_sum hterm
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp [hN0.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
