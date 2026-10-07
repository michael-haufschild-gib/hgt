import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSquareMass
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Weighted square summability for the literal arithmetic coefficients

The already proved square-mass bounds imply finite coefficient energy on
each line strictly right of one half, for both the reciprocal and its zeta
quotient. This is a coefficient statement, with no actual-line mean identity
or uniform boundedness asserted for the quotient.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem summable_square_weight_of_mass {b : ℕ → ℂ} {r σ C : ℝ}
    (hr : 0 ≤ r) (hσ : r < 2 * σ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 ≤
      C * ((N : ℝ) + 1) ^ r) :
    Summable (fun n : ℕ => ‖b n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) := by
  have hL : LSeriesSummable (fun n => ((‖b n‖ ^ 2 : ℝ) : ℂ)) ((2 * σ : ℝ) : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := r) _ (fun _ => sq_nonneg _)
      hr (by simpa using hσ)
    refine Asymptotics.IsBigO.of_bound (C * 2 ^ r) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) r)]
    calc
      _ ≤ C * ((N : ℝ) + 1) ^ r := hbound N
      _ ≤ C * (2 * (N : ℝ)) ^ r := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) hr) hC
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
  refine hL.norm.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero, norm_zero, Nat.cast_zero,
      Real.zero_rpow (by linarith : -2 * σ ≠ 0), mul_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', norm_div,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_of_nonneg (sq_nonneg _),
      Complex.ofReal_re, show -2 * σ = -(2 * σ) by ring,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Full positivity alone gives finite reciprocal coefficient energy at
every real part strictly greater than one half. -/
theorem summable_reciprocal_square_weight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ =>
      ‖producerMobius (fun n => if 2 ≤ n then lam n else 0) n‖ ^ 2 *
        (n : ℝ) ^ (-2 * σ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_reciprocal_square_mass_le hW
    (show 0 < σ - 1 / 2 by linarith)
  exact summable_square_weight_of_mass (by linarith : 0 ≤ 1 + (σ - 1 / 2))
    (by linarith) hC hbound

/-- The literal quotient coefficients also have finite weighted square
energy. Actual quotient mean values require a separate argument. -/
theorem summable_quotient_square_weight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ =>
      ‖LSeries.convolution 1 (producerMobius (fun n => if 2 ≤ n then lam n else 0)) n‖ ^ 2 *
        (n : ℝ) ^ (-2 * σ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_quotient_square_mass_le hW
    (show 0 < σ - 1 / 2 by linarith)
  exact summable_square_weight_of_mass (by linarith : 0 ≤ 1 + (σ - 1 / 2))
    (by linarith) hC hbound

end RHTower.WeilSingularArithmetic
