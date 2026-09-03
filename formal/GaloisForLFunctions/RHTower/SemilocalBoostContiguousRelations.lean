import GaloisForLFunctions.RHTower.SemilocalDiagonalPfaffTransformation

/-!
# Two contiguous relations for the σ-form hypergeometric sums

With `F_n = ₂F₁(−n, n+½; ½; x)`, `H_n = ₂F₁(−n, n+3/2; ½; x)`, `K_n = ₂F₁(−n, n+5/2; 3/2; x)`
(terminating sums, `hypSumSq`):

* `(2n+1) F_{n+1} + 2(n+1) F_n = (4n+3)(1 − x) H_n`   (the difference `S_{n+1} − S_n` of the diagonal),
* `H_{n+1} − H_n = −(4n+5) x K_n`                     (the difference of the smooth sequence `H`).

Both are proved coefficientwise from the recursions of the falling and rising factorials.  They are
the Jacobi contiguous relations `P_{n+1}^{(0,−½)} − P_n^{(0,−½)} ∝ (1−y) P_n^{(1,−½)}` and
`P_{n+1}^{(−½,1)} − P_n^{(−½,1)} ∝ (1+y) P_n^{(½,1)}` in hypergeometric form.
-/

open Finset
open scoped BigOperators

namespace RHTower

namespace ScaledHypergeometric

/-- The `l`-th coefficient of `hypSumSq n d c`. -/
noncomputable def hypCoeff (n : ℕ) (d c : ℝ) (l : ℕ) : ℝ :=
  (-1) ^ l * fallingNat n l * rising ((n : ℝ) + d) l / (rising c l * l.factorial)

theorem hypSumSq_eq_sum_hypCoeff (n : ℕ) (d c x : ℝ) :
    hypSumSq n d c x = ∑ l ∈ range (n + 1), hypCoeff n d c l * x ^ l := rfl

theorem hypCoeff_eq_zero_of_lt {n l : ℕ} (h : n < l) (d c : ℝ) : hypCoeff n d c l = 0 := by
  unfold hypCoeff
  rw [fallingNat_eq_zero_of_lt h]
  ring

theorem hypCoeff_zero (n : ℕ) (d c : ℝ) : hypCoeff n d c 0 = 1 := by
  simp [hypCoeff, fallingNat, rising]

/-- Sums may be extended one step beyond the degree. -/
theorem hypSumSq_eq_sum_range_succ (n : ℕ) (d c x : ℝ) :
    hypSumSq n d c x = ∑ l ∈ range (n + 2), hypCoeff n d c l * x ^ l := by
  rw [hypSumSq_eq_sum_hypCoeff, sum_range_succ _ (n + 1), hypCoeff_eq_zero_of_lt (by omega)]
  ring

/-- The shifted coefficient sequence of `x · hypSumSq`. -/
noncomputable def hypShiftCoeff (n : ℕ) (d c : ℝ) (l : ℕ) : ℝ :=
  if l = 0 then 0 else hypCoeff n d c (l - 1)

theorem mul_hypSumSq_eq_sum_shift (n : ℕ) (d c x : ℝ) :
    x * hypSumSq n d c x = ∑ l ∈ range (n + 2), hypShiftCoeff n d c l * x ^ l := by
  rw [hypSumSq_eq_sum_hypCoeff, mul_sum, sum_range_succ' _ (n + 1)]
  simp only [hypShiftCoeff, if_true, zero_mul, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
  apply sum_congr rfl
  intro l _
  ring

/-! ## Recursions of the factorials -/

theorem fallingNat_succ (n l : ℕ) : fallingNat n (l + 1) = fallingNat n l * ((n : ℝ) - l) := by
  simp [fallingNat, prod_range_succ]

theorem fallingNat_succ_succ (n l : ℕ) : fallingNat (n + 1) (l + 1) = ((n : ℝ) + 1) * fallingNat n l := by
  unfold fallingNat
  rw [prod_range_succ']
  simp only [Nat.cast_zero, sub_zero, Nat.cast_succ]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro i _
  ring

/-! ## The first contiguous relation -/

theorem contiguous_F_coeff (n l : ℕ) :
    (2 * (n : ℝ) + 1) * hypCoeff (n + 1) (1 / 2) (1 / 2) l +
        2 * ((n : ℝ) + 1) * hypCoeff n (1 / 2) (1 / 2) l =
      (4 * (n : ℝ) + 3) * (hypCoeff n (3 / 2) (1 / 2) l - hypShiftCoeff n (3 / 2) (1 / 2) l) := by
  cases l with
  | zero =>
      simp only [hypCoeff_zero, hypShiftCoeff, if_true]
      ring
  | succ l =>
      simp only [hypShiftCoeff, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      unfold hypCoeff
      push_cast
      rw [fallingNat_succ_succ, fallingNat_succ, rising_succ ((n : ℝ) + 1 + 1 / 2),
        rising_succ' ((n : ℝ) + 1 / 2), rising_succ ((n : ℝ) + 3 / 2), rising_succ (1 / 2),
        Nat.factorial_succ, show ((n : ℝ) + 1 + 1 / 2) = (n : ℝ) + 3 / 2 by ring,
        show ((n : ℝ) + 1 / 2 + 1) = (n : ℝ) + 3 / 2 by ring]
      have h1 : rising (1 / 2) l ≠ 0 := (rising_pos (by norm_num) l).ne'
      have h2 : (1 / 2 : ℝ) + l ≠ 0 := by positivity
      have h3 : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
      have h4 : ((l : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- **First contiguous relation:** `(2n+1) F_{n+1} + 2(n+1) F_n = (4n+3)(1 − x) H_n`. -/
theorem contiguous_F (n : ℕ) (x : ℝ) :
    (2 * (n : ℝ) + 1) * hypSumSq (n + 1) (1 / 2) (1 / 2) x +
        2 * ((n : ℝ) + 1) * hypSumSq n (1 / 2) (1 / 2) x =
      (4 * (n : ℝ) + 3) * (1 - x) * hypSumSq n (3 / 2) (1 / 2) x := by
  have hF1 := hypSumSq_eq_sum_hypCoeff (n + 1) (1 / 2) (1 / 2) x
  have hF0 := hypSumSq_eq_sum_range_succ n (1 / 2) (1 / 2) x
  have hH := hypSumSq_eq_sum_range_succ n (3 / 2) (1 / 2) x
  have hxH := mul_hypSumSq_eq_sum_shift n (3 / 2) (1 / 2) x
  rw [show (4 * (n : ℝ) + 3) * (1 - x) * hypSumSq n (3 / 2) (1 / 2) x =
      (4 * (n : ℝ) + 3) * (hypSumSq n (3 / 2) (1 / 2) x - x * hypSumSq n (3 / 2) (1 / 2) x) by ring,
    hxH, hF1, hF0, hH, mul_sum, mul_sum, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  have := contiguous_F_coeff n l
  linear_combination (x ^ l) * this

/-! ## The second contiguous relation -/

theorem contiguous_H_coeff (n l : ℕ) :
    hypCoeff (n + 1) (3 / 2) (1 / 2) l - hypCoeff n (3 / 2) (1 / 2) l =
      -(4 * (n : ℝ) + 5) * hypShiftCoeff n (5 / 2) (3 / 2) l := by
  cases l with
  | zero =>
      simp only [hypCoeff_zero, hypShiftCoeff, if_true]
      ring
  | succ l =>
      simp only [hypShiftCoeff, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      unfold hypCoeff
      push_cast
      rw [fallingNat_succ_succ, fallingNat_succ, rising_succ ((n : ℝ) + 1 + 3 / 2),
        rising_succ' ((n : ℝ) + 3 / 2), rising_succ' (1 / 2),
        Nat.factorial_succ, show ((n : ℝ) + 1 + 3 / 2) = (n : ℝ) + 5 / 2 by ring,
        show ((n : ℝ) + 3 / 2 + 1) = (n : ℝ) + 5 / 2 by ring,
        show ((1 / 2 : ℝ) + 1) = 3 / 2 by norm_num]
      have h1 : rising (3 / 2) l ≠ 0 := (rising_pos (by norm_num) l).ne'
      have h3 : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
      have h4 : ((l : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- **Second contiguous relation:** `H_{n+1} − H_n = −(4n+5) x K_n`. -/
theorem contiguous_H (n : ℕ) (x : ℝ) :
    hypSumSq (n + 1) (3 / 2) (1 / 2) x - hypSumSq n (3 / 2) (1 / 2) x =
      -(4 * (n : ℝ) + 5) * (x * hypSumSq n (5 / 2) (3 / 2) x) := by
  rw [hypSumSq_eq_sum_hypCoeff (n + 1), hypSumSq_eq_sum_range_succ n (3 / 2) (1 / 2) x,
    mul_hypSumSq_eq_sum_shift, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro l _
  have := contiguous_H_coeff n l
  linear_combination (x ^ l) * this

end ScaledHypergeometric

end RHTower
