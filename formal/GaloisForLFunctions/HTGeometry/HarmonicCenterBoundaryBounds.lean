import GaloisForLFunctions.HTGeometry.HarmonicTailSquareIdentity
import GaloisForLFunctions.HTGeometry.FiniteHarmonicRows

/-!
# Square control of the harmonic center boundary

The upper harmonic increment is at most one. The lower boundary has the exact
square mass `2N-H_N`. Together these give a quadratic weighted bound for the
remainder left when the center-density matrix cancels the pole rows.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- An upper harmonic increment of length at most its starting point is at most one. -/
theorem harmonic_add_sub_le_one {n N : ℕ} (hnN : n ≤ N) :
    (harmonic (N + n) : ℝ) - harmonic N ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sum_Icc_one_div_add N n]
  calc
    (∑ j ∈ Icc 1 n, 1 / ((N : ℝ) + j)) ≤ ∑ _j ∈ Icc 1 n, 1 / (n : ℝ) := by
      refine sum_le_sum fun j hj => one_div_le_one_div_of_le hnR ?_
      have hNj : (n : ℝ) ≤ N := by exact_mod_cast hnN
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith only [hNj, hj0]
    _ = 1 := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp [hnR.ne']

theorem harmonic_add_sub_nonneg (N n : ℕ) :
    0 ≤ (harmonic (N + n) : ℝ) - harmonic N := by
  rw [← sum_Icc_one_div_add N n]
  exact sum_nonneg fun j _ => by positivity

private theorem harmonic_real_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact sum_nonneg fun j _ => by positivity

private theorem center_boundary_sq_le (a b d : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) : ((a - b) / 2 + d) ^ 2 ≤ a ^ 2 + 4 := by
  have hb2 : b ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg hb (sub_nonneg.mpr hb1), hb1]
  have hd2 : d ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg hd (sub_nonneg.mpr hd1), hd1]
  have hcs : (a - b + 2 * d) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + 4 * d ^ 2) := by
    nlinarith only [sq_nonneg (a + b), sq_nonneg (a - 2 * d), sq_nonneg (b + 2 * d)]
  nlinarith only [hcs, hb2, hd2, sq_nonneg a]

/-- The exact center-row boundary remainder has uniformly quadratic weighted mass. -/
theorem sum_weighted_sq_harmonic_center_boundary_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n : ℝ) *
      ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
        3 / (4 * (n : ℝ))) ^ 2) ≤ 6 * (N : ℝ) ^ 2 := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
        3 / (4 * (n : ℝ))) ^ 2 ≤
      ((harmonic N : ℝ) - harmonic (N - n)) ^ 2 + 4 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have h := center_boundary_sq_le
      ((harmonic N : ℝ) - harmonic (N - n))
      ((harmonic (N + n) : ℝ) - harmonic N) (3 / (4 * (n : ℝ)))
      (harmonic_add_sub_nonneg N n) (harmonic_add_sub_le_one (mem_Icc.mp hn).2)
      (by positivity) (by rw [div_le_one (by positivity)]; linarith only [hn1])
    convert h using 1
    ring
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) *
        (((harmonic N : ℝ) - harmonic (N - n)) ^ 2 + 4) := by
      refine sum_le_sum fun n hn => ?_
      exact (mul_le_mul_of_nonneg_left (hterm n hn) (Nat.cast_nonneg n)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hn).2) (by positivity))
    _ = (N : ℝ) * (2 * (N : ℝ) - harmonic N + 4 * (N : ℝ)) := by
      rw [← mul_sum, sum_add_distrib, sum_sq_harmonic_boundary_tails]
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ 6 * (N : ℝ) ^ 2 := by
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (harmonic_real_nonneg N)]

end GaloisForLFunctions.HTGeometry
