import GaloisForLFunctions.HTGeometry.FiniteWeightedGroundStateBound

/-!
# Uniform finite-horizon bounds for the two pole outer products

The sum of the reciprocal-square-root and square-root outer products has
quadratic-form cost at most twice the squared horizon. On a bounded pole-gauge
profile its squared output is at most four times the fourth horizon power.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

private theorem sqrt_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Real.sqrt (n : ℝ) := by
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  simpa only [Real.sqrt_one] using h

private theorem sqrt_le_nat {n : ℕ} (hn : 1 ≤ n) : Real.sqrt (n : ℝ) ≤ n := by
  have h1 := sqrt_ge_one hn
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hs, mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (sub_nonneg.mpr h1)]

/-- Each positive-horizon pole kernel entry is bounded by twice the horizon. -/
theorem twoPoleKernel_le_two_horizon {n j N : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n ≤ 2 * (N : ℝ) := by
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
  have hnj : Real.sqrt (n : ℝ) / Real.sqrt j ≤ N :=
    (div_le_self (Real.sqrt_nonneg _) (sqrt_ge_one (mem_Icc.mp hj).1)).trans
      ((sqrt_le_nat (mem_Icc.mp hn).1).trans hnN)
  have hjn : Real.sqrt (j : ℝ) / Real.sqrt n ≤ N :=
    (div_le_self (Real.sqrt_nonneg _) (sqrt_ge_one (mem_Icc.mp hn).1)).trans
      ((sqrt_le_nat (mem_Icc.mp hj).1).trans hjN)
  linarith only [hnj, hjn]

/-- A scalar error multiplying both pole outer products has uniform form control. -/
theorem abs_twoPoleKernel_quadratic_le (N : ℕ) (x : ℕ → ℝ) (d : ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      x n * x j * (d * (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n))| ≤
      2 * |d| * (N : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  let K : ℕ → ℕ → ℝ := fun n j =>
    |d| * (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)
  have hK : ∀ n j, 0 ≤ K n j := fun n j => by dsimp only [K]; positivity
  have hrow {n : ℕ} (hn : n ∈ Icc 1 N) :
      (∑ j ∈ Icc 1 N, K n j) ≤ 2 * |d| * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _j ∈ Icc 1 N, |d| * (2 * (N : ℝ)) :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (twoPoleKernel_le_two_horizon hn hj) (abs_nonneg _)
      _ = _ := by
        simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  have hschur := finite_weighted_schur_row_potential (Icc 1 N) (fun n => |x n|)
    (fun _ => (1 : ℝ)) K (fun _ _ => zero_lt_one)
    (fun n _ j _ => hK n j) (fun n _ j _ => by dsimp only [K]; ring)
  simp only [div_one, mul_one, sq_abs] at hschur
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |x n| * |x j| * K n j := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
      have h := abs_sum_le_sum_abs
        (fun j => x n * x j * (d * (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)))
        (Icc 1 N)
      refine h.trans_eq (sum_congr rfl fun j _ => ?_)
      dsimp only [K]
      simp only [abs_mul]
      rw [abs_of_nonneg (show 0 ≤ Real.sqrt (n : ℝ) / Real.sqrt j +
        Real.sqrt j / Real.sqrt n by positivity)]
    _ ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * ∑ j ∈ Icc 1 N, K n j := hschur
    _ ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * (2 * |d| * (N : ℝ) ^ 2) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow hn) (sq_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- The two-pole kernel acts on bounded pole-gauge profiles at square-root row scale. -/
theorem abs_twoPoleKernel_poleProfile_row_le {a : ℕ → ℝ} {A : ℝ} {N n : ℕ}
    (hA : 0 ≤ A) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A) (hn : n ∈ Icc 1 N) :
    |∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * (a j / Real.sqrt j)| ≤
      2 * A * (N : ℝ) * Real.sqrt n := by
  have hsn1 := sqrt_ge_one (mem_Icc.mp hn).1
  have hsn0 : 0 < Real.sqrt (n : ℝ) := by linarith only [hsn1]
  have hterm (j : ℕ) (hj : j ∈ Icc 1 N) :
      |(Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * (a j / Real.sqrt j)| ≤
        2 * A * Real.sqrt n := by
    have hsj1 := sqrt_ge_one (mem_Icc.mp hj).1
    have hsj0 : 0 < Real.sqrt (j : ℝ) := by linarith only [hsj1]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    have heq : (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * (a j / Real.sqrt j) =
        Real.sqrt n * (a j / j) + a j / Real.sqrt n := by
      calc
        _ = (Real.sqrt n * a j) / (Real.sqrt j * Real.sqrt j) +
            (Real.sqrt j / Real.sqrt j) * (a j / Real.sqrt n) := by ring
        _ = _ := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg j), div_self hsj0.ne', one_mul]
          ring
    have hsmall : |a j / j| ≤ A := by
      rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)]
      exact (div_le_div_of_nonneg_right (ha j hj) (Nat.cast_nonneg j)).trans
        (div_le_self hA hj1)
    have hrec : 1 / Real.sqrt (n : ℝ) ≤ Real.sqrt n :=
      (div_le_self zero_le_one hsn1).trans hsn1
    rw [heq]
    calc
      _ ≤ Real.sqrt n * |a j / j| + |a j| / Real.sqrt n := by
        simpa only [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))]
          using abs_add_le (Real.sqrt n * (a j / j)) (a j / Real.sqrt n)
      _ ≤ Real.sqrt n * A + A / Real.sqrt n := add_le_add
        (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _))
        (div_le_div_of_nonneg_right (ha j hj) hsn0.le)
      _ ≤ 2 * A * Real.sqrt n := by
        have h := mul_le_mul_of_nonneg_left hrec hA
        rw [mul_one_div] at h
        linarith only [h]
  calc
    _ ≤ ∑ _j ∈ Icc 1 N, 2 * A * Real.sqrt n :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- Squared action on a bounded pole profile has at most fourth-power horizon growth. -/
theorem sum_sq_twoPoleKernel_poleProfile_le {a : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (N : ℕ) (ha : ∀ j ∈ Icc 1 N, |a j| ≤ A) (d : ℝ) :
    (∑ n ∈ Icc 1 N, (d * ∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * (a j / Real.sqrt j)) ^ 2) ≤
      4 * d ^ 2 * A ^ 2 * (N : ℝ) ^ 4 := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      (d * ∑ j ∈ Icc 1 N,
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * (a j / Real.sqrt j)) ^ 2 ≤
      d ^ 2 * (2 * A * (N : ℝ)) ^ 2 * (N : ℝ) := by
    have h := abs_twoPoleKernel_poleProfile_row_le hA ha hn
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    rw [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hs
    rw [mul_pow]
    have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg d)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have ht := mul_le_mul_of_nonneg_left hnN
      (mul_nonneg (sq_nonneg d) (sq_nonneg (2 * A * (N : ℝ))))
    nlinarith only [hmul, ht]
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, d ^ 2 * (2 * A * (N : ℝ)) ^ 2 * (N : ℝ) :=
      sum_le_sum hterm
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

end GaloisForLFunctions.HTGeometry
