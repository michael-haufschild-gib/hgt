import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifier
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalLowerAsymptotic
import GaloisForLFunctions.RHTower.EntireDirichletPolynomial

/-!
# Shifted entire form of the linear Levinson mollifier

The mean-square calculation uses coefficients normalized on the critical line.  Littlewood's
rectangle uses an entire Dirichlet polynomial.  Multiplication of the coefficient at `n` by
`n^sigma` makes evaluation at `sigma + it` exactly the critical-line polynomial, while retaining
unit head, real coefficients, and the coefficient bounds required by `LevinsonMeanSquareGate`.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Entire-polynomial coefficient whose restriction to `Re s = sigma` is the literal linear
Levinson mollifier. -/
def levinsonShiftedLinearMollifierCoeff (M : ℕ) (sigma : ℝ) (n : ℕ) : ℂ :=
  (((n : ℝ) ^ sigma : ℝ) : ℂ) * Sieve.levinsonLinearMollifierCoeff M n

@[simp] theorem star_levinsonShiftedLinearMollifierCoeff
    (M : ℕ) (sigma : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (levinsonShiftedLinearMollifierCoeff M sigma n) =
      levinsonShiftedLinearMollifierCoeff M sigma n := by
  rw [levinsonShiftedLinearMollifierCoeff, map_mul, Complex.conj_ofReal,
    Sieve.star_levinsonLinearMollifierCoeff]

/-- The shifted mollifier retains unit head. -/
theorem levinsonShiftedLinearMollifierCoeff_one
    {M : ℕ} (hM : 1 < M) (sigma : ℝ) :
    levinsonShiftedLinearMollifierCoeff M sigma 1 = 1 := by
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hM)).ne'
  rw [levinsonShiftedLinearMollifierCoeff,
    Sieve.levinsonLinearMollifierCoeff, Sieve.barbanVehovWeight_one hM.le]
  norm_num [hlog]

/-- On the Levinson strip the shifted entire coefficients have norm at most one. -/
theorem norm_levinsonShiftedLinearMollifierCoeff_le_one
    {M n : ℕ} (hM : 1 < M) (hn : 1 ≤ n) {sigma : ℝ}
    (hsigma : sigma ≤ 1 / 2) :
    ‖levinsonShiftedLinearMollifierCoeff M sigma n‖ ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  rw [levinsonShiftedLinearMollifierCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)]
  calc
    (n : ℝ) ^ sigma * ‖Sieve.levinsonLinearMollifierCoeff M n‖ ≤
        (n : ℝ) ^ sigma * (1 / Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (Sieve.norm_levinsonLinearMollifierCoeff_le hM)
        (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)
    _ = (n : ℝ) ^ (sigma - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hnpos.le,
        ← Real.rpow_add hnpos]
      congr 1
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)

/-- Crude polynomial mass bound in exactly the gate's `n^4` norm. -/
theorem sum_norm_levinsonShiftedLinearMollifierCoeff_mul_pow_four_le
    {M : ℕ} (hM : 1 < M) {sigma : ℝ}
    (hsigma : sigma ≤ 1 / 2) :
    (∑ n ∈ Finset.Icc 1 M,
        ‖levinsonShiftedLinearMollifierCoeff M sigma n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤
      ((M + 1 : ℕ) : ℝ) ^ 5 := by
  calc
    (∑ n ∈ Finset.Icc 1 M,
        ‖levinsonShiftedLinearMollifierCoeff M sigma n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤
      ∑ n ∈ Finset.Icc 1 M, ((M + 1 : ℕ) : ℝ) ^ 4 := by
        refine Finset.sum_le_sum fun n hnmem => ?_
        have hnI := Finset.mem_Icc.mp hnmem
        have hcoeff := norm_levinsonShiftedLinearMollifierCoeff_le_one
          hM hnI.1 hsigma
        have hnle : (n : ℝ) ≤ (M + 1 : ℕ) := by exact_mod_cast (hnI.2.trans (Nat.le_succ M))
        have hpow : (n : ℝ) ^ (4 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg n) hnle (by norm_num)
        calc
          ‖levinsonShiftedLinearMollifierCoeff M sigma n‖ * (n : ℝ) ^ (4 : ℝ) ≤
              1 * (n : ℝ) ^ (4 : ℝ) :=
            mul_le_mul_of_nonneg_right hcoeff
              (Real.rpow_nonneg (Nat.cast_nonneg n) 4)
          _ ≤ 1 * ((M + 1 : ℕ) : ℝ) ^ (4 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
          _ = ((M + 1 : ℕ) : ℝ) ^ (4 : ℝ) := one_mul _
        all_goals norm_num [Real.rpow_natCast]
    _ ≤ ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) ^ 4 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      gcongr
      have hcard : (Finset.Icc 1 M).card ≤ M + 1 := by
        exact (Finset.card_le_card (Finset.Icc_subset_Icc (Nat.zero_le 1) le_rfl)).trans_eq
          (Nat.card_Icc 0 M)
      exact_mod_cast hcard
    _ = ((M + 1 : ℕ) : ℝ) ^ 5 := by ring

/-- On `Re s = sigma`, the shifted entire polynomial is exactly the critical-line-normalized
Levinson mollifier. -/
theorem edPoly_levinsonShiftedLinearMollifierCoeff_line
    (M : ℕ) (sigma t : ℝ) :
    edPoly (levinsonShiftedLinearMollifierCoeff M sigma) (Finset.Icc 1 M)
        ((sigma : ℂ) + (t : ℂ) * I) =
      Sieve.levinsonLinearMollifier M t := by
  rw [edPoly_line _ (fun n hn => (Finset.mem_Icc.mp hn).1),
    Sieve.levinsonLinearMollifier_eq_sum]
  unfold cdpoly cdterm
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [levinsonShiftedLinearMollifierCoeff]
  have hcancel : (n : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) = 1 := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hcancelC : (((n : ℝ) ^ sigma : ℝ) : ℂ) *
      (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcancel
  calc
    (((n : ℝ) ^ sigma : ℝ) : ℂ) * Sieve.levinsonLinearMollifierCoeff M n *
          (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
          Complex.exp (((-(Real.log n) * t : ℝ) : ℂ) * I) =
        ((((n : ℝ) ^ sigma : ℝ) : ℂ) * (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)) *
          Sieve.levinsonLinearMollifierCoeff M n *
          Complex.exp (((-(Real.log n) * t : ℝ) : ℂ) * I) := by ring
    _ = Sieve.levinsonLinearMollifierCoeff M n *
          Complex.exp (((-(Real.log n) * t : ℝ) : ℂ) * I) := by rw [hcancelC]; ring

end

end RHTower
