import GaloisForLFunctions.HTGeometry.ClogVertLog
import GaloisForLFunctions.HTGeometry.ComplexLogTaylorUniform

/-!
# From a vanishing order to a power bound

The general Stirling ladder reduces to a polynomial statement: the rational part of the one-step
difference is `P(u)/(1+u)^k` with `P` a polynomial, and the rung is exactly the assertion that the
coefficients can be chosen so that `X^N ∣ P`.

This module supplies the analytic half of that reduction, once and for all: a polynomial divisible
by `X^N` gives a genuine `O(‖u‖^N)` bound on `‖u‖ ≤ ½`, with the constant explicit in the
coefficients of the cofactor.  The denominator costs only `2^k`, since `‖1+u‖ ≥ ½` there.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

theorem one_half_le_norm_one_add {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) : (1 : ℝ) / 2 ≤ ‖1 + u‖ := by
  have hb := norm_sub_le ((1 : ℂ) + u) u
  rw [add_sub_cancel_right, norm_one] at hb
  linarith

/-- **A polynomial vanishing to order `N` is `O(‖u‖^N)` on the half disc**, even after division by
a power of `1 + u`. -/
theorem exists_norm_polyEval_div_pow_le_of_dvd {P : Polynomial ℂ} {N : ℕ}
    (h : (Polynomial.X ^ N : Polynomial ℂ) ∣ P) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ ≤ 1 / 2 →
      ‖P.eval u / (1 + u) ^ k‖ ≤ C * ‖u‖ ^ N := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨(∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖) * 2 ^ k,
    by positivity, fun u hu => ?_⟩
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hlow := one_half_le_norm_one_add hu
  have hpos : (0 : ℝ) < ‖1 + u‖ := by linarith
  have hQb := norm_polyEval_le_of_norm_le_one Q (by linarith : ‖u‖ ≤ 1)
  have heval : P.eval u = u ^ N * Q.eval u := by
    rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [heval, norm_div, norm_mul]
  simp only [norm_pow]
  have hpk : (1 : ℝ) ≤ 2 ^ k * ‖1 + u‖ ^ k := by
    calc (1 : ℝ) = (2 * (1 / 2 : ℝ)) ^ k := by norm_num
      _ ≤ (2 * ‖1 + u‖) ^ k := pow_le_pow_left₀ (by norm_num) (by linarith) k
      _ = 2 ^ k * ‖1 + u‖ ^ k := by rw [mul_pow]
  have hdenpos : (0 : ℝ) < ‖1 + u‖ ^ k := by positivity
  rw [div_le_iff₀ hdenpos]
  have hQ0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hstep : ‖u‖ ^ N * ‖Q.eval u‖
      ≤ ‖u‖ ^ N * (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖) :=
    mul_le_mul_of_nonneg_left hQb (by positivity)
  calc ‖u‖ ^ N * ‖Q.eval u‖
      ≤ ‖u‖ ^ N * (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖) := hstep
    _ ≤ ‖u‖ ^ N * (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖)
        * (2 ^ k * ‖1 + u‖ ^ k) := by
        nlinarith [hpk, mul_nonneg (pow_nonneg hu0 N) hQ0]
    _ = (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖) * 2 ^ k * ‖u‖ ^ N
        * ‖1 + u‖ ^ k := by ring

end

end GaloisForLFunctions.HTGeometry
