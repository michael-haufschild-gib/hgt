import GaloisForLFunctions.HTGeometry.GammaShiftLadderGraded
import GaloisForLFunctions.HTGeometry.GammaShiftLadderDifference

/-!
# The leading coefficient of the ladder polynomial

Two facts already proved combine to pin the ladder coefficients down completely:

* `natDegree_shiftLadderCoeffPoly_le`: `d_M` is a polynomial in the shift of degree at most `M+1`;
* `shiftLadderCoeff_succ_sub`: its forward difference is `-(-μ)^M`.

The forward difference of a polynomial of degree `≤ M+1` reads off its top coefficient with the
factor `M+1`, so the top coefficient is forced to be `(-1)^{M+1}/(M+1)` — in particular it is
nonzero, which is the triangularity the power-sum reading needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- **The top coefficient of the `M`-th ladder polynomial.** -/
theorem shiftLadderCoeffPoly_coeff_top (M : ℕ) :
    (shiftLadderCoeffPoly M).coeff (M + 1) = (-1 : ℂ) ^ (M + 1) / ((M : ℂ) + 1) := by
  set p := shiftLadderCoeffPoly M with hpdef
  have hdeg : p.natDegree ≤ M + 1 := natDegree_shiftLadderCoeffPoly_le M
  have hsum : p = ∑ i ∈ Finset.range (M + 2), Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [p.as_sum_range' (M + 2) (by omega)]
    exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial.symm
  set q : Polynomial ℂ :=
    ∑ i ∈ Finset.range (M + 2), Polynomial.C (p.coeff i) * (1 + Polynomial.X) ^ i with hqdef
  have hqeval : ∀ mu : ℂ, q.eval mu = p.eval (mu + 1) := by
    intro mu
    rw [hqdef, Polynomial.eval_finsetSum]
    conv_rhs => rw [hsum]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [add_comm]
  have hdiff : ∀ mu : ℂ, p.eval (mu + 1) - p.eval mu = -((-mu) ^ M) := by
    intro mu
    rw [hpdef, ← shiftLadderCoeff_eq_eval, ← shiftLadderCoeff_eq_eval]
    exact shiftLadderCoeff_succ_sub mu M
  have hpoly : q - p = Polynomial.C (-((-1 : ℂ) ^ M)) * Polynomial.X ^ M := by
    refine Polynomial.funext fun r => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [hqeval r, hdiff r, neg_pow]
    ring
  have hcoeff : q.coeff M = p.coeff M + p.coeff (M + 1) * ((M : ℂ) + 1) := by
    rw [hqdef, Polynomial.finsetSum_coeff]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hzero : ∀ i ∈ Finset.range M,
        (Polynomial.C (p.coeff i) * (1 + Polynomial.X) ^ i).coeff M = 0 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt hi]
      simp
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
      Polynomial.coeff_one_add_X_pow, Nat.choose_self, Nat.choose_succ_self_right]
    push_cast
    ring
  have hfin : p.coeff (M + 1) * ((M : ℂ) + 1) = -((-1 : ℂ) ^ M) := by
    have h1 : (q - p).coeff M = p.coeff (M + 1) * ((M : ℂ) + 1) := by
      rw [Polynomial.coeff_sub, hcoeff]; ring
    rw [hpoly, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h1
    simpa using h1.symm
  have hne : ((M : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_add_one_ne_zero (R := ℂ) M
    simpa using h
  have hsign : ((-1 : ℂ)) ^ (M + 1) = -((-1 : ℂ) ^ M) := by rw [pow_succ]; ring
  rw [hsign, eq_div_iff hne]
  exact hfin

/-- The top coefficient is nonzero: the ladder polynomial has degree exactly `M+1`. -/
theorem shiftLadderCoeffPoly_coeff_top_ne_zero (M : ℕ) :
    (shiftLadderCoeffPoly M).coeff (M + 1) ≠ 0 := by
  rw [shiftLadderCoeffPoly_coeff_top]
  have hne : ((M : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_add_one_ne_zero (R := ℂ) M
    simpa using h
  have hnum : ((-1 : ℂ)) ^ (M + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact div_ne_zero hnum hne

/-- **The ladder polynomial has degree exactly `M+1`.** -/
theorem natDegree_shiftLadderCoeffPoly (M : ℕ) :
    (shiftLadderCoeffPoly M).natDegree = M + 1 := by
  refine le_antisymm (natDegree_shiftLadderCoeffPoly_le M) ?_
  exact Polynomial.le_natDegree_of_ne_zero (shiftLadderCoeffPoly_coeff_top_ne_zero M)

end

end GaloisForLFunctions.HTGeometry
