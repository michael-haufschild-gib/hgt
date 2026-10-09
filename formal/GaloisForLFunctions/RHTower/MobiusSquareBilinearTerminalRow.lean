import GaloisForLFunctions.RHTower.MobiusSquareResidueShortBilinear

set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction

namespace RHTower

private theorem square_terminal_weighted_inverse {X : ℕ} (hX : 1 ≤ X) (w : ℕ → ℝ) :
    (∑ b ∈ Icc 1 X, (moebius b : ℝ) * ∑ k ∈ Icc 1 (X / b), w (b * k)) =
      w 1 := by
  have hmu (n : ℕ) :
      (∑ x ∈ n.divisorsAntidiagonal, (moebius x.1 : ℝ)) =
        if n = 1 then 1 else 0 := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun i _ => (moebius i : ℝ))]
    rw [← Int.cast_sum, sum_moebius_divisors]
    split_ifs <;> simp
  calc
    _ = ∑ b ∈ Icc 1 X, ∑ k ∈ Icc 1 (X / b), (moebius b : ℝ) * w (b * k) := by
      simp only [mul_sum]
    _ = ∑ n ∈ Icc 1 X, ∑ x ∈ n.divisorsAntidiagonal,
        (moebius x.1 : ℝ) * w (x.1 * x.2) :=
      (Sieve.sum_Icc_divisorsAntidiagonal_swap
        (fun b k => (moebius b : ℝ) * w (b * k)) X).symm
    _ = ∑ n ∈ Icc 1 X, (if n = 1 then 1 else 0) * w n := by
      apply sum_congr rfl
      intro n _
      calc
        _ = ∑ x ∈ n.divisorsAntidiagonal, (moebius x.1 : ℝ) * w n := by
          apply sum_congr rfl
          intro x hx
          rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
        _ = _ := by rw [← sum_mul, hmu]
    _ = w 1 := by simp [hX]

/-- Although the literal kernel is indefinite, its terminal row against the
actual Möbius vector collapses by exact divisor inversion. -/
theorem mobiusSquareShortBilinearKernel_terminal_moebius_row {N : ℕ} (hN : 1 ≤ N) :
    (∑ b ∈ Icc 1 N, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (N * b)) =
      Real.log N * mobiusSquareFloorPrefix N N := by
  have hN0 : N ≠ 0 := by omega
  have hdiv : N ^ 2 / N = N := by simp [pow_two, hN0]
  have hcut (b : ℕ) : N ^ 2 / (N * b) = N / b := by
    rw [← Nat.div_div_eq_div_mul, hdiv]
  simpa only [mobiusSquareShortBilinearKernel, hcut, Nat.mul_assoc, Nat.mul_one] using
    square_terminal_weighted_inverse hN
      (fun n => Real.log (N * n : ℕ) * mobiusSquareFloorPrefix N (N * n))

/-- Exact cancellation of the terminal row's main term. -/
theorem mobiusSquareShortBilinearKernel_terminal_centered_row {N : ℕ} (hN : 1 ≤ N) :
    (∑ b ∈ Icc 1 N, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (N * b)) -
        Real.log N / N * (∑ s ∈ range N, (s : ℝ) ^ 2) =
      -(Real.log N / N * quadraticResiduePrefix N N) := by
  rw [mobiusSquareShortBilinearKernel_terminal_moebius_row hN]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hv := quadraticResiduePrefix_add_mul_floor N N
  rw [← hv]
  field_simp [hN0]
  ring

theorem mobiusSquareShortBilinearKernel_terminal_centered_row_nonpos
    {N : ℕ} (hN : 1 ≤ N) :
    (∑ b ∈ Icc 1 N, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (N * b)) -
        Real.log N / N * (∑ s ∈ range N, (s : ℝ) ^ 2) ≤ 0 := by
  rw [mobiusSquareShortBilinearKernel_terminal_centered_row hN]
  apply neg_nonpos.mpr
  apply mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (Nat.cast_nonneg N))
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The terminal centered row is below the critical quadratic scale. -/
theorem abs_mobiusSquareShortBilinearKernel_terminal_centered_row_le
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ b ∈ Icc 1 N, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (N * b)) -
        Real.log N / N * (∑ s ∈ range N, (s : ℝ) ^ 2)| ≤
      (N : ℝ) * Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV0 : 0 ≤ quadraticResiduePrefix N N := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hV : quadraticResiduePrefix N N ≤ (N : ℝ) ^ 2 := by
    unfold quadraticResiduePrefix
    calc
      _ ≤ ∑ _s ∈ range N, (N : ℝ) := by
        apply sum_le_sum
        intro s _
        exact_mod_cast (Nat.mod_lt (s ^ 2) (show 0 < N by omega)).le
      _ = _ := by simp [pow_two]
  rw [mobiusSquareShortBilinearKernel_terminal_centered_row hN, abs_neg,
    abs_of_nonneg (mul_nonneg
      (div_nonneg (Real.log_natCast_nonneg N) hNpos.le) hV0)]
  calc
    _ ≤ Real.log N / N * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hV (div_nonneg (Real.log_natCast_nonneg N) hNpos.le)
    _ = _ := by field_simp

theorem abs_mobiusSquareShortBilinearKernel_terminal_centered_row_le_quadratic
    {N : ℕ} (hN : 1 ≤ N) :
    |(∑ b ∈ Icc 1 N, (moebius b : ℝ) * mobiusSquareShortBilinearKernel N (N * b)) -
        Real.log N / N * (∑ s ∈ range N, (s : ℝ) ^ 2)| ≤ (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log (N : ℝ) ≤ N := by
    have h := Real.log_le_sub_one_of_pos hNpos
    linarith
  calc
    _ ≤ (N : ℝ) * Real.log N := abs_mobiusSquareShortBilinearKernel_terminal_centered_row_le hN
    _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left hlog hNpos.le
    _ = _ := by ring

end RHTower
