import GaloisForLFunctions.ArithmeticIntersectionTheory.TheTowerFormOfAPrime

/-!
# Exact weighted squares for the finite number-minus-tower form

The geometric tails give the Blaschke coefficients without an infinite limit.
Weighted telescoping separates the single ground term from the positive
integer-weighted excitation squares.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory Finset

private theorem sum_range_succ_weight_sub (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, ((j : ℝ) + 1) * (f j - f (j + 1))) =
      (∑ j ∈ range N, f j) - (N : ℝ) * f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The finite actual form splits into one negative ground term and all positive
Blaschke excitation squares. The algebraic identity holds for every real parameter. -/
theorem towerNumberForm_eq_weighted_squares (q : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    (∑ j ∈ range N, ((j : ℝ) + 1) * x j ^ 2) - kmsForm q N x =
      -(q ^ 2) * towerTail q N x 0 ^ 2 +
        ∑ j ∈ range N, ((j : ℝ) + 1) *
          (q * towerTail q N x j - towerTail q N x (j + 1)) ^ 2 := by
  have hterm (j : ℕ) (hj : j ∈ range N) :
      x j ^ 2 - (q * towerTail q N x j - towerTail q N x (j + 1)) ^ 2 =
        (1 - q ^ 2) * (towerTail q N x j ^ 2 - towerTail q N x (j + 1) ^ 2) := by
    have hx := towerTail_eq q (mem_range.mp hj) x
    rw [show x j = towerTail q N x j - q * towerTail q N x (j + 1) by linarith only [hx]]
    ring
  have hsum :
      (∑ j ∈ range N, ((j : ℝ) + 1) * x j ^ 2) -
        (∑ j ∈ range N, ((j : ℝ) + 1) *
          (q * towerTail q N x j - towerTail q N x (j + 1)) ^ 2) =
      (1 - q ^ 2) * (∑ j ∈ range N, towerTail q N x j ^ 2) := by
    rw [← sum_sub_distrib]
    calc
      _ = (1 - q ^ 2) * ∑ j ∈ range N, ((j : ℝ) + 1) *
          (towerTail q N x j ^ 2 - towerTail q N x (j + 1) ^ 2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [← mul_sub, hterm j hj]
        ring
      _ = _ := by rw [sum_range_succ_weight_sub, towerTail_self]; ring
  rw [sum_towerTail_sq] at hsum
  rw [kmsForm_eq_tail]
  linear_combination hsum

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
