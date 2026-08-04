import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Explicit growth bounds for two-variable polynomials

A two-variable polynomial evaluated at `(z, w)` is bounded by the sum of its coefficient norms times
`(1 + ‖z‖)` and `(1 + ‖w‖)` to the total degree.

This is the numerator estimate for any comparison between an algebraic relation among functions and
their growth: the coefficients of a relation between two states are two-variable polynomials, so the
bound they impose is polynomial in the two maximum moduli.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Classical in
/-- The sum of the norms of a multivariate polynomial's coefficients. -/
noncomputable def mvCoeffNormSum {σ : Type*} (P : MvPolynomial σ ℂ) : ℝ :=
  ∑ m ∈ P.support, ‖MvPolynomial.coeff m P‖

theorem mvCoeffNormSum_nonneg {σ : Type*} (P : MvPolynomial σ ℂ) : 0 ≤ mvCoeffNormSum P := by
  classical
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Each exponent of a monomial in the support is at most the total degree. -/
theorem exponent_le_totalDegree {σ : Type*} {P : MvPolynomial σ ℂ} {m : σ →₀ ℕ}
    (hm : m ∈ P.support) (i : σ) : m i ≤ P.totalDegree := by
  classical
  refine le_trans ?_ (MvPolynomial.le_totalDegree hm)
  by_cases hi : i ∈ m.support
  · exact Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact Nat.zero_le _

/-- **An explicit growth bound for a two-variable polynomial.** -/
theorem norm_eval_le_mvCoeffNormSum (P : MvPolynomial (Fin 2) ℂ) (z w : ℂ) :
    ‖MvPolynomial.eval ![z, w] P‖
      ≤ mvCoeffNormSum P * (1 + ‖z‖) ^ P.totalDegree * (1 + ‖w‖) ^ P.totalDegree := by
  classical
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by
    have := norm_nonneg z
    linarith
  have hw1 : (1 : ℝ) ≤ 1 + ‖w‖ := by
    have := norm_nonneg w
    linarith
  rw [MvPolynomial.eval_eq']
  refine le_trans (norm_sum_le _ _) ?_
  rw [mvCoeffNormSum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro m hm
  have hprod : ∏ i : Fin 2, (![z, w] : Fin 2 → ℂ) i ^ m i = z ^ m 0 * w ^ m 1 := by
    rw [Fin.prod_univ_two]
    rfl
  have hz : ‖z‖ ^ m 0 ≤ (1 + ‖z‖) ^ P.totalDegree := by
    calc ‖z‖ ^ m 0 ≤ (1 + ‖z‖) ^ m 0 :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖z‖) ^ P.totalDegree :=
          pow_le_pow_right₀ hz1 (exponent_le_totalDegree hm 0)
  have hw : ‖w‖ ^ m 1 ≤ (1 + ‖w‖) ^ P.totalDegree := by
    calc ‖w‖ ^ m 1 ≤ (1 + ‖w‖) ^ m 1 :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖w‖) ^ P.totalDegree :=
          pow_le_pow_right₀ hw1 (exponent_le_totalDegree hm 1)
  calc ‖MvPolynomial.coeff m P * ∏ i : Fin 2, (![z, w] : Fin 2 → ℂ) i ^ m i‖
      = ‖MvPolynomial.coeff m P‖ * (‖z‖ ^ m 0 * ‖w‖ ^ m 1) := by
        rw [hprod, norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ ‖MvPolynomial.coeff m P‖
          * ((1 + ‖z‖) ^ P.totalDegree * (1 + ‖w‖) ^ P.totalDegree) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul hz hw (by positivity) (by positivity)
    _ = ‖MvPolynomial.coeff m P‖ * (1 + ‖z‖) ^ P.totalDegree * (1 + ‖w‖) ^ P.totalDegree := by
        ring

/-! ## The logarithmic form -/

open Real in
/-- **The two-variable growth bound in logarithmic form.**  This is the shape a proximity estimate
consumes: `log⁺` of a polynomial value is bounded by `log⁺` of the two arguments, with the total
degree as the multiplier. -/
theorem posLog_norm_eval_le (A : MvPolynomial (Fin 2) ℂ) (z w : ℂ) :
    Real.posLog ‖MvPolynomial.eval ![z, w] A‖
      ≤ Real.posLog (mvCoeffNormSum A)
        + A.totalDegree * (Real.log 2 + Real.posLog ‖z‖)
        + A.totalDegree * (Real.log 2 + Real.posLog ‖w‖) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hC0 : 0 ≤ mvCoeffNormSum A := mvCoeffNormSum_nonneg A
  have hprod0 : (0 : ℝ) ≤ mvCoeffNormSum A * (1 + ‖z‖) ^ A.totalDegree
      * (1 + ‖w‖) ^ A.totalDegree := by positivity
  have h1 : Real.posLog ‖MvPolynomial.eval ![z, w] A‖
      ≤ Real.posLog (mvCoeffNormSum A * (1 + ‖z‖) ^ A.totalDegree
        * (1 + ‖w‖) ^ A.totalDegree) :=
    Real.monotoneOn_posLog (Set.mem_Ici.mpr (norm_nonneg _)) (Set.mem_Ici.mpr hprod0)
      (norm_eval_le_mvCoeffNormSum A z w)
  have h2 : Real.posLog (mvCoeffNormSum A * (1 + ‖z‖) ^ A.totalDegree
      * (1 + ‖w‖) ^ A.totalDegree)
      ≤ Real.posLog (mvCoeffNormSum A) + Real.posLog ((1 + ‖z‖) ^ A.totalDegree)
        + Real.posLog ((1 + ‖w‖) ^ A.totalDegree) := by
    refine le_trans Real.posLog_mul ?_
    have := Real.posLog_mul (x := mvCoeffNormSum A) (y := (1 + ‖z‖) ^ A.totalDegree)
    linarith
  have hzstep : Real.posLog ((1 + ‖z‖) ^ A.totalDegree)
      ≤ A.totalDegree * (Real.log 2 + Real.posLog ‖z‖) := by
    rw [Real.posLog_pow]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have := Real.posLog_add (x := (1 : ℝ)) (y := ‖z‖)
    rw [Real.posLog_one] at this
    linarith
  have hwstep : Real.posLog ((1 + ‖w‖) ^ A.totalDegree)
      ≤ A.totalDegree * (Real.log 2 + Real.posLog ‖w‖) := by
    rw [Real.posLog_pow]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have := Real.posLog_add (x := (1 : ℝ)) (y := ‖w‖)
    rw [Real.posLog_one] at this
    linarith
  linarith

end GaloisForLFunctions.HTGeometry
