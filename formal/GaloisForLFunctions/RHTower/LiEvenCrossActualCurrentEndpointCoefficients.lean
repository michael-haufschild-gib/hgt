import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelInteriorFirstZero
import Mathlib.Algebra.Polynomial.Taylor

open Polynomial Complex
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Endpoint-normalized odd Chebyshev polynomial for actual current mode `n`. -/
def liEvenCrossNormalizedEndpointPolynomial (n : ℕ) : Polynomial ℝ :=
  C (1 / (2 * ((n + 1 : ℕ) : ℝ))) *
    (Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp (1 - 2 * X)

private theorem factorial_odd_product (j : ℕ) :
    (2 * j + 1).factorial =
      2 ^ j * j.factorial * ∏ i ∈ Finset.range j, (2 * i + 3) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, ih, Nat.factorial_succ,
      pow_succ, Finset.prod_range_succ]
    ring

private theorem liEvenCrossNormalizedEndpointPolynomial_coeff_derivative (n j : ℕ) :
    (liEvenCrossNormalizedEndpointPolynomial n).coeff j =
      (-2 : ℝ) ^ j *
        ((derivative^[j] (Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ))).eval 1) /
        (2 * ((n + 1 : ℕ) : ℝ) * (j.factorial : ℝ)) := by
  let p := Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)
  have hc : p.comp (1 - 2 * X) = (p.taylor 1).comp (C (-2) * X) := by
    rw [taylor_apply, comp_assoc]
    congr 1
    have htwo : C (2 : ℝ) = (2 : Polynomial ℝ) := rfl
    simp [htwo]
    ring
  have hd : (j.factorial : ℝ) * (hasseDeriv j p).eval 1 =
      (derivative^[j] p).eval 1 := by
    have h := congrArg (fun q : Polynomial ℝ => q.eval 1)
      (congrFun (factorial_smul_hasseDeriv (R := ℝ) (k := j)) p)
    simpa using h
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hn : (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  change (C (1 / (2 * ((n + 1 : ℕ) : ℝ))) * p.comp (1 - 2 * X)).coeff j = _
  rw [hc, coeff_C_mul, comp_C_mul_X_coeff, taylor_coeff]
  rw [← hd]
  field_simp

/-- Exact finite endpoint coefficients, including automatic truncation. -/
theorem liEvenCrossNormalizedEndpointPolynomial_coeff (n j : ℕ) :
    (liEvenCrossNormalizedEndpointPolynomial n).coeff j =
      (-1 : ℝ) ^ j * 4 ^ j *
        (∏ i ∈ Finset.range j,
          (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2)) /
        ((2 * j + 1).factorial : ℝ) := by
  rw [liEvenCrossNormalizedEndpointPolynomial_coeff_derivative,
    Chebyshev.iterate_derivative_U_eval_one_eq_div]
  have hf := congrArg (fun k : ℕ => (k : ℝ)) (factorial_odd_product j)
  push_cast at hf
  have hp : (((∏ i ∈ Finset.range j,
      ((((2 * n + 1 : ℕ) : ℤ) + 1) ^ 2 - ((i : ℤ) + 1) ^ 2)) : ℤ) : ℝ) =
      ∏ i ∈ Finset.range j,
        (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2) := by
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hp, hf]
  push_cast
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hn : (2 * ((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hp0 : (∏ i ∈ Finset.range j, ((2 * i + 3 : ℕ) : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    positivity
  rw [show (-2 : ℝ) = (-1) * 2 by norm_num, mul_pow]
  rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ j * 2 ^ j by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]]
  field_simp
  ring

/-- Factorial majorant valid at every degree and every mode. -/
theorem norm_liEvenCrossNormalizedEndpointPolynomial_coeff_le (n j : ℕ) :
    ‖(liEvenCrossNormalizedEndpointPolynomial n).coeff j‖ ≤
      (16 * ((n + 1 : ℕ) : ℝ) ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) := by
  by_cases hj : j < 2 * (n + 1)
  · have hf : ∀ i ∈ Finset.range j,
        ‖4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2‖ ≤
          4 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      intro i hi
      have hi' : ((i + 1 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show i + 1 ≤ 2 * (n + 1) by
          have := Finset.mem_range.mp hi
          omega)
      have hnon : 0 ≤ 4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (2 * ((n + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ))]
      rw [Real.norm_of_nonneg hnon]
      nlinarith [sq_nonneg (((i + 1 : ℕ) : ℝ))]
    have hp : ‖∏ i ∈ Finset.range j,
        (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2)‖ ≤
        (4 * ((n + 1 : ℕ) : ℝ) ^ 2) ^ j := by
      rw [norm_prod]
      simpa only [Finset.prod_const, Finset.card_range] using
        Finset.prod_le_prod (fun i hi => norm_nonneg _) hf
    rw [liEvenCrossNormalizedEndpointPolynomial_coeff]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), Real.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      4 ^ j * ‖∏ i ∈ Finset.range j,
          (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2)‖ ≤
          4 ^ j * (4 * ((n + 1 : ℕ) : ℝ) ^ 2) ^ j :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (16 * ((n + 1 : ℕ) : ℝ) ^ 2) ^ j := by
        rw [← mul_pow]
        congr 1
        ring
  · have hp : (∏ i ∈ Finset.range j,
        (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2)) = 0 := by
      apply Finset.prod_eq_zero (i := 2 * n + 1)
      · exact Finset.mem_range.mpr (by omega)
      · push_cast
        ring
    rw [liEvenCrossNormalizedEndpointPolynomial_coeff, hp]
    simp only [mul_zero, zero_div, norm_zero]
    positivity

private theorem eval_normalizedEndpointPolynomial (n : ℕ) (x : ℂ) :
    evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x =
      (Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval (1 - 2 * x) /
        (2 * ((n + 1 : ℕ) : ℂ)) := by
  simp only [liEvenCrossNormalizedEndpointPolynomial, evalRealPolynomial,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_ofNat,
    Polynomial.map_X, Chebyshev.map_U, eval_mul, eval_C, eval_comp,
    eval_sub, eval_one, eval_ofNat, eval_X, map_div₀, map_one, map_mul,
    map_ofNat, map_natCast]
  push_cast
  ring

/-- Exact normalized actual atom. Both radial factors survive source transport. -/
theorem liEvenCrossSquareMassAdjacentFlux_div_eq_normalizedEndpointPolynomial
    {v : ℝ} (hv : 0 < v) (n : ℕ) (q : XiZeroCopy) :
    liEvenCrossSquareMassAdjacentFlux v n q /
        (2 * ((n + 1 : ℕ) : ℂ) ^ 2) =
      xiZeroCopyReciprocalSquare q *
        (1 - (v : ℂ) * xiShiftedReciprocalSquare v q) ^ 2 *
          evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n)
            ((v : ℂ) * xiShiftedReciprocalSquare v q) := by
  let x : ℂ := (v : ℂ) * xiShiftedReciprocalSquare v q
  have hu : (Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval (2 * x - 1) =
      -(Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval (1 - 2 * x) := by
    rw [show 2 * x - 1 = -(1 - 2 * x) by ring, Chebyshev.U_eval_neg]
    simp [Int.negOnePow_two_mul_add_one]
  have hf : liEvenCrossSquareMassAdjacentFlux v n q =
      xiShiftedReciprocalSquare v q * ((n + 1 : ℕ) : ℂ) * (1 - x) *
        (Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval (1 - 2 * x) := by
    rw [liEvenCrossSquareMassAdjacentFlux_eq_unitFluxQuotient hv,
      liEvenCrossUnitFluxQuotient_eq_oddChebyshev]
    change xiShiftedReciprocalSquare v q *
      evalRealPolynomial
        (-((n : Polynomial ℝ) + 1) * (1 - X) *
          (Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp liEvenCrossUnitAffine) x = _
    simp only [evalRealPolynomial, Polynomial.map_mul, Polynomial.map_neg,
      Polynomial.map_add, Polynomial.map_natCast, Polynomial.map_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_comp, Chebyshev.map_U,
      eval_mul, eval_neg, eval_add, eval_natCast, eval_one, eval_sub, eval_X, eval_comp]
    simp only [liEvenCrossUnitAffine, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one,
      eval_sub, eval_mul, eval_ofNat, eval_X, eval_one]
    rw [hu]
    push_cast
    ring
  have ha : xiShiftedReciprocalSquare v q = xiZeroCopyReciprocalSquare q * (1 - x) := by
    dsimp [x, xiShiftedReciprocalSquare]
    have hd : 1 + xiZeroCopyReciprocalSquare q * (v : ℂ) ≠ 0 := by
      simpa only [mul_comm] using one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hv.le q
    field_simp [one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hv.le q, hd]
    ring
  change liEvenCrossSquareMassAdjacentFlux v n q / (2 * ((n + 1 : ℕ) : ℂ) ^ 2) =
    xiZeroCopyReciprocalSquare q * (1 - x) ^ 2 *
      evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x
  rw [hf, ha, eval_normalizedEndpointPolynomial]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

end
end RHTower
