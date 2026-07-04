/-
Finite cumulant/exponential truncation infrastructure for the MWM spur multiplier.

`SpurRescale` proves analytic inequalities for

    φ_d(j) = ∏_{i<j} (1 - i/d).

This file packages the algebraic side of doc 34 Lemma R/R1: the logarithmic cumulant
truncation as a polynomial in `T = 1/d`, the formal truncation of `exp (-x)`, and the
composite multiplier polynomial whose coefficients are the finite-order `e_p(j)`.
-/
import GaloisForLFunctions.RHTower.SpurRescale

namespace RHTower

open Polynomial

noncomputable section

/-- Positive logarithmic cumulant truncation in the formal variable `T = 1 / d`.

The signed logarithmic approximation to `φ_d(j)` is `-cumulantLogPoly n j` evaluated
at `T = 1/d`. -/
def cumulantLogPoly (n j : ℕ) : ℝ[X] :=
  ∑ l ∈ Finset.range n,
    Polynomial.C (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) * Polynomial.X ^ (l + 1)

/-- Exponential truncation for `exp (-x)`, through powers `< P`. -/
def expNegTruncPoly (P : ℕ) : ℝ[X] :=
  ∑ p ∈ Finset.range P,
    Polynomial.C (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) * Polynomial.X ^ p

/-- R1's finite multiplier polynomial: the formal truncation of
`exp (-(positive cumulants))`. -/
def multiplierTruncPoly (P n j : ℕ) : ℝ[X] :=
  (expNegTruncPoly P).comp (cumulantLogPoly n j)

/-- Coefficient notation for the finite multiplier expansion.  These are the `e_p(j)`
coefficients from doc 34 R1, after choosing truncation orders `P` and `n`. -/
def multiplierCoeff (P n j p : ℕ) : ℝ :=
  (multiplierTruncPoly P n j).coeff p

/-- Evaluate the positive logarithmic cumulant polynomial. -/
theorem eval_cumulantLogPoly (n j : ℕ) (t : ℝ) :
    (cumulantLogPoly n j).eval t =
      ∑ l ∈ Finset.range n,
        (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) * t ^ (l + 1) := by
  rw [cumulantLogPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluate the exponential truncation polynomial. -/
theorem eval_expNegTruncPoly (P : ℕ) (x : ℝ) :
    (expNegTruncPoly P).eval x =
      ∑ p ∈ Finset.range P, (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) * x ^ p := by
  rw [expNegTruncPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluate the finite multiplier polynomial as a composed truncation. -/
theorem eval_multiplierTruncPoly (P n j : ℕ) (t : ℝ) :
    (multiplierTruncPoly P n j).eval t =
      (expNegTruncPoly P).eval ((cumulantLogPoly n j).eval t) := by
  rw [multiplierTruncPoly, Polynomial.eval_comp]

/-- Fully expanded finite-sum form of the multiplier truncation. -/
theorem eval_multiplierTruncPoly_expanded (P n j : ℕ) (t : ℝ) :
    (multiplierTruncPoly P n j).eval t =
      ∑ p ∈ Finset.range P,
        (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) *
          ((∑ l ∈ Finset.range n,
            (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) * t ^ (l + 1)) ^ p) := by
  rw [eval_multiplierTruncPoly, eval_expNegTruncPoly, eval_cumulantLogPoly]

/-- The logarithmic cumulant polynomial has degree at most its truncation order. -/
theorem natDegree_cumulantLogPoly_le (n j : ℕ) :
    (cumulantLogPoly n j).natDegree ≤ n := by
  rw [cumulantLogPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l hl => ?_)
  have hln : l + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hl)
  calc
    (Polynomial.C (rescalePowerSum (l + 1) j / (l + 1 : ℝ)) *
        Polynomial.X ^ (l + 1)).natDegree
        ≤ (Polynomial.C (rescalePowerSum (l + 1) j / (l + 1 : ℝ))).natDegree +
            (Polynomial.X ^ (l + 1 : ℕ)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ n := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      omega

/-- The `exp (-x)` truncation has degree at most its term count. -/
theorem natDegree_expNegTruncPoly_le (P : ℕ) :
    (expNegTruncPoly P).natDegree ≤ P := by
  rw [expNegTruncPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun p hp => ?_)
  have hpP : p ≤ P := Nat.le_of_lt (Finset.mem_range.mp hp)
  calc
    (Polynomial.C (((-1 : ℝ) ^ p) / (p.factorial : ℝ)) * Polynomial.X ^ p).natDegree
        ≤ (Polynomial.C (((-1 : ℝ) ^ p) / (p.factorial : ℝ))).natDegree +
            (Polynomial.X ^ p).natDegree := Polynomial.natDegree_mul_le
    _ ≤ P := by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      omega

/-- Degree filtration for the finite multiplier coefficients. -/
theorem natDegree_multiplierTruncPoly_le (P n j : ℕ) :
    (multiplierTruncPoly P n j).natDegree ≤ P * n := by
  rw [multiplierTruncPoly, Polynomial.natDegree_comp]
  exact Nat.mul_le_mul (natDegree_expNegTruncPoly_le P) (natDegree_cumulantLogPoly_le n j)

/-- Coefficient-sum expansion over a fixed range large enough for the whole truncation.

This is the algebraic carrier for the finite `Σ e_p(j) / d^p` side of R1. -/
theorem eval_multiplierTruncPoly_coeff_sum (P n j : ℕ) (t : ℝ) :
    (multiplierTruncPoly P n j).eval t =
      ∑ p ∈ Finset.range (P * n + 1), multiplierCoeff P n j p * t ^ p := by
  rw [show (∑ p ∈ Finset.range (P * n + 1), multiplierCoeff P n j p * t ^ p) =
      ∑ p ∈ Finset.range (P * n + 1), (multiplierTruncPoly P n j).coeff p * t ^ p by
        simp [multiplierCoeff]]
  exact Polynomial.eval_eq_sum_range' (p := multiplierTruncPoly P n j) (x := t)
    (by exact Nat.lt_succ_of_le (natDegree_multiplierTruncPoly_le P n j))

end

end RHTower
