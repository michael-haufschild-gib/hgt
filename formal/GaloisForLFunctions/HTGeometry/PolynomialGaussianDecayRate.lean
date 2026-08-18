import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Quantitative decay of a polynomial against a Gaussian

A real polynomial times `e^{-x²}` decays faster than every inverse power, with a completely explicit
constant: outside the unit interval `|p(x)| ≤ (∑|coeff|)·|x|^{deg p}`, while the exponential-series
bound `t^N e^{-t} ≤ N!` at `t = x²` absorbs the remaining `|x|^{deg p + k}`.  The resulting estimate

```text
|p(x)| e^{-x²}  ≤  (∑|coeff|) · (deg p + k)! / |x|^k     for `1 ≤ |x|`
```

is what turns a qualitative "polynomial-Gaussian tends to zero" statement into a rate.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Coefficient mass of a real polynomial. -/
def polyCoeffMass (p : Polynomial ℝ) : ℝ := ∑ d ∈ p.support, |p.coeff d|

theorem polyCoeffMass_nonneg (p : Polynomial ℝ) : 0 ≤ polyCoeffMass p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Outside the unit interval a polynomial is bounded by its coefficient mass times the degree
power of the argument. -/
theorem abs_eval_le_polyCoeffMass_mul_pow (p : Polynomial ℝ) {x : ℝ} (hx : 1 ≤ |x|) :
    |p.eval x| ≤ polyCoeffMass p * |x| ^ p.natDegree := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [polyCoeffMass, Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  have hdj : d ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp d hd
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hdj) (abs_nonneg _)

/-- **A polynomial against a Gaussian decays faster than every inverse power.**  Outside the unit
interval the product `|p| e^{-x²}` is bounded by an explicit constant divided by `|x|^k`, the
constant being the coefficient mass times a factorial of the degree and the exponent. -/
theorem abs_eval_mul_exp_neg_sq_le (p : Polynomial ℝ) (k : ℕ) {x : ℝ} (hx : 1 ≤ |x|) :
    |p.eval x| * Real.exp (-x ^ 2)
      ≤ polyCoeffMass p * ((p.natDegree + k).factorial : ℝ) / |x| ^ k := by
  have hx0 : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hx
  have hpk : (0 : ℝ) < |x| ^ k := pow_pos hx0 k
  have hA : 0 ≤ polyCoeffMass p := polyCoeffMass_nonneg p
  have hexp : (0 : ℝ) < Real.exp (-x ^ 2) := Real.exp_pos _
  rw [le_div_iff₀ hpk]
  have h1 : |p.eval x| ≤ polyCoeffMass p * |x| ^ p.natDegree :=
    abs_eval_le_polyCoeffMass_mul_pow p hx
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hfac : (x ^ 2) ^ (p.natDegree + k) * Real.exp (-x ^ 2)
      ≤ ((p.natDegree + k).factorial : ℝ) := by
    have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    have h := Real.pow_div_factorial_le_exp (x ^ 2) hx2 (p.natDegree + k)
    have hfac0 : (0 : ℝ) < ((p.natDegree + k).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hfac0] at h
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-x ^ 2)).le
    have hcancel : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (x ^ 2) ^ (p.natDegree + k) * Real.exp (-x ^ 2)
        ≤ Real.exp (x ^ 2) * ((p.natDegree + k).factorial : ℝ) * Real.exp (-x ^ 2) := hmul
      _ = ((p.natDegree + k).factorial : ℝ) * (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) := by ring
      _ = ((p.natDegree + k).factorial : ℝ) := by rw [hcancel, mul_one]
  have hxpow : |x| ^ (p.natDegree + k) ≤ (x ^ 2) ^ (p.natDegree + k) := by
    rw [hsq, ← pow_mul]
    exact pow_le_pow_right₀ hx (by omega)
  calc |p.eval x| * Real.exp (-x ^ 2) * |x| ^ k
      ≤ polyCoeffMass p * |x| ^ p.natDegree * Real.exp (-x ^ 2) * |x| ^ k := by
        have := mul_le_mul_of_nonneg_right h1 hexp.le
        exact mul_le_mul_of_nonneg_right this hpk.le
    _ = polyCoeffMass p * (|x| ^ (p.natDegree + k) * Real.exp (-x ^ 2)) := by
        rw [pow_add]; ring
    _ ≤ polyCoeffMass p * ((x ^ 2) ^ (p.natDegree + k) * Real.exp (-x ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        exact mul_le_mul_of_nonneg_right hxpow hexp.le
    _ ≤ polyCoeffMass p * ((p.natDegree + k).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hfac hA


/-- **The same at an arbitrary Gaussian rate.**  Outside the unit interval,
`|p| e^{-b x²} ≤ (∑|coeff|)·(deg p + k)! / (b^{deg p + k} |x|^k)`. -/
theorem abs_eval_mul_exp_neg_mul_sq_le (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) (k : ℕ)
    {x : ℝ} (hx : 1 ≤ |x|) :
    |p.eval x| * Real.exp (-(b * x ^ 2))
      ≤ polyCoeffMass p * ((p.natDegree + k).factorial : ℝ) / b ^ (p.natDegree + k)
          / |x| ^ k := by
  have hx0 : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hx
  have hpk : (0 : ℝ) < |x| ^ k := pow_pos hx0 k
  have hA : 0 ≤ polyCoeffMass p := polyCoeffMass_nonneg p
  have hexp : (0 : ℝ) < Real.exp (-(b * x ^ 2)) := Real.exp_pos _
  have hbN : (0 : ℝ) < b ^ (p.natDegree + k) := pow_pos hb _
  rw [le_div_iff₀ hpk]
  have h1 : |p.eval x| ≤ polyCoeffMass p * |x| ^ p.natDegree :=
    abs_eval_le_polyCoeffMass_mul_pow p hx
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hfac : (x ^ 2) ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2))
      ≤ ((p.natDegree + k).factorial : ℝ) / b ^ (p.natDegree + k) := by
    have hx2 : (0 : ℝ) ≤ b * x ^ 2 := by positivity
    have h := Real.pow_div_factorial_le_exp (b * x ^ 2) hx2 (p.natDegree + k)
    have hfac0 : (0 : ℝ) < ((p.natDegree + k).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hfac0] at h
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(b * x ^ 2))).le
    have hcancel : Real.exp (b * x ^ 2) * Real.exp (-(b * x ^ 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hstep : (b * x ^ 2) ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2))
        ≤ ((p.natDegree + k).factorial : ℝ) := by
      calc (b * x ^ 2) ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2))
          ≤ Real.exp (b * x ^ 2) * ((p.natDegree + k).factorial : ℝ)
              * Real.exp (-(b * x ^ 2)) := hmul
        _ = ((p.natDegree + k).factorial : ℝ)
              * (Real.exp (b * x ^ 2) * Real.exp (-(b * x ^ 2))) := by ring
        _ = ((p.natDegree + k).factorial : ℝ) := by rw [hcancel, mul_one]
    rw [le_div_iff₀ hbN]
    calc (x ^ 2) ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2)) * b ^ (p.natDegree + k)
        = (b * x ^ 2) ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2)) := by
          rw [mul_pow]; ring
      _ ≤ ((p.natDegree + k).factorial : ℝ) := hstep
  have hxpow : |x| ^ (p.natDegree + k) ≤ (x ^ 2) ^ (p.natDegree + k) := by
    rw [hsq, ← pow_mul]
    exact pow_le_pow_right₀ hx (by omega)
  calc |p.eval x| * Real.exp (-(b * x ^ 2)) * |x| ^ k
      ≤ polyCoeffMass p * |x| ^ p.natDegree * Real.exp (-(b * x ^ 2)) * |x| ^ k := by
        have := mul_le_mul_of_nonneg_right h1 hexp.le
        exact mul_le_mul_of_nonneg_right this hpk.le
    _ = polyCoeffMass p * (|x| ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2))) := by
        rw [pow_add]; ring
    _ ≤ polyCoeffMass p * ((x ^ 2) ^ (p.natDegree + k) * Real.exp (-(b * x ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        exact mul_le_mul_of_nonneg_right hxpow hexp.le
    _ ≤ polyCoeffMass p * (((p.natDegree + k).factorial : ℝ) / b ^ (p.natDegree + k)) :=
        mul_le_mul_of_nonneg_left hfac hA
    _ = polyCoeffMass p * ((p.natDegree + k).factorial : ℝ) / b ^ (p.natDegree + k) := by
        ring

end GaloisForLFunctions.HTGeometry

end
