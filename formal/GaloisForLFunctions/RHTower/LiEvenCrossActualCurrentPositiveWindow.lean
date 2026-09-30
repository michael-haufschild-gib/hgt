import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentEndpointCoefficients
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import Mathlib.Algebra.Ring.GeomSum

/-!
# A uniform positive window for the actual LI current

The endpoint coefficient envelope controls the complete multiplicity-exact
current when `(n + 1)^2 * v ≤ 25`. No later moment sign is assumed.
-/

open Polynomial Complex
open scoped BigOperators

namespace RHTower
noncomputable section

private theorem factorial_tail_lower (j : ℕ) :
    6 * 20 ^ j ≤ (2 * j + 3).factorial := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hp : 20 ≤ (2 * j + 5) * (2 * j + 4) := by nlinarith
    have hf : (2 * (j + 1) + 3).factorial =
        (2 * j + 5) * (2 * j + 4) * (2 * j + 3).factorial := by
      rw [show 2 * (j + 1) + 3 = (2 * j + 3) + 1 + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [hf, pow_succ]
    nlinarith [Nat.mul_le_mul_left 20 ih,
      Nat.mul_le_mul_right (2 * j + 3).factorial hp]

private theorem fixed_factorial_majorant (j : ℕ) :
    (8 / 3 : ℝ) ^ (j + 1) / ((2 * j + 3).factorial : ℝ) ≤
      (4 / 9 : ℝ) * (2 / 15 : ℝ) ^ j := by
  have hf : (6 : ℝ) * 20 ^ j ≤ ((2 * j + 3).factorial : ℝ) := by
    exact_mod_cast factorial_tail_lower j
  calc
    (8 / 3 : ℝ) ^ (j + 1) / ((2 * j + 3).factorial : ℝ) ≤
        (8 / 3 : ℝ) ^ (j + 1) / (6 * 20 ^ j) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hf
    _ = (4 / 9 : ℝ) * (2 / 15 : ℝ) ^ j := by
      rw [show (2 / 15 : ℝ) = (8 / 3) / 20 by norm_num]
      simp only [div_pow, pow_succ]
      field_simp
      ring

private theorem normalizedEndpointPolynomial_error_le
    (n : ℕ) (x : ℂ)
    (hx : 16 * ((n + 1 : ℕ) : ℝ) ^ 2 * ‖x‖ ≤ 8 / 3) :
    ‖evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1‖ ≤ 20 / 39 := by
  let p := liEvenCrossNormalizedEndpointPolynomial n
  have hp0 : p.coeff 0 = 1 := by
    simp [p, liEvenCrossNormalizedEndpointPolynomial_coeff]
  have heval : evalRealPolynomial p x =
      ∑ j ∈ Finset.range (p.natDegree + 1), (p.coeff j : ℂ) * x ^ j := by
    rw [evalRealPolynomial, ← eval₂_eq_eval_map, eval₂_eq_sum_range]
    rfl
  have heq : evalRealPolynomial p x - 1 =
      ∑ j ∈ Finset.range p.natDegree, (p.coeff (j + 1) : ℂ) * x ^ (j + 1) := by
    rw [heval, Finset.sum_range_succ', hp0]
    simp
  have hterm (j : ℕ) : ‖(p.coeff (j + 1) : ℂ) * x ^ (j + 1)‖ ≤
      (4 / 9 : ℝ) * (2 / 15 : ℝ) ^ j := by
    rw [norm_mul, Complex.norm_real, norm_pow]
    have hc := norm_liEvenCrossNormalizedEndpointPolynomial_coeff_le n (j + 1)
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega] at hc
    calc
      ‖p.coeff (j + 1)‖ * ‖x‖ ^ (j + 1) ≤
          ((16 * ((n + 1 : ℕ) : ℝ) ^ 2) ^ (j + 1) /
            ((2 * j + 3).factorial : ℝ)) * ‖x‖ ^ (j + 1) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (16 * ((n + 1 : ℕ) : ℝ) ^ 2 * ‖x‖) ^ (j + 1) /
          ((2 * j + 3).factorial : ℝ) := by rw [mul_pow]; ring
      _ ≤ (8 / 3 : ℝ) ^ (j + 1) / ((2 * j + 3).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx _) (by positivity)
      _ ≤ (4 / 9 : ℝ) * (2 / 15 : ℝ) ^ j := fixed_factorial_majorant j
  have hgeom := geom_sum_mul_of_le_one (show (2 / 15 : ℝ) ≤ 1 by norm_num) p.natDegree
  have hsum : ∑ j ∈ Finset.range p.natDegree,
      (4 / 9 : ℝ) * (2 / 15 : ℝ) ^ j ≤ 20 / 39 := by
    rw [← Finset.mul_sum]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 15) p.natDegree]
  rw [heq]
  exact (norm_sum_le _ _).trans
    ((Finset.sum_le_sum (fun j hj => hterm j)).trans hsum)

private theorem actual_current_atom_error_le
    {v : ℝ} (hv : 0 < v) (n : ℕ)
    (hwindow : ((n + 1 : ℕ) : ℝ) ^ 2 * v ≤ 25) (q : XiZeroCopy) :
    ‖liEvenCrossSquareMassAdjacentFlux v n q /
        (2 * ((n + 1 : ℕ) : ℂ) ^ 2) - xiZeroCopyReciprocalSquare q‖ ≤
      (409 / 468 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ := by
  let x : ℂ := (v : ℂ) * xiShiftedReciprocalSquare v q
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hv25 : v ≤ 25 := by
    have hs : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs hv.le]
  have hx : ‖x‖ ≤ v / 150 := by
    dsimp [x]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.le]
    calc
      v * ‖xiShiftedReciprocalSquare v q‖ ≤ v * ‖xiZeroCopyReciprocalSquare q‖ :=
        mul_le_mul_of_nonneg_left (norm_xiShiftedReciprocalSquare_le hv.le q) hv.le
      _ ≤ v * (1 / 150) := mul_le_mul_of_nonneg_left
        (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le hv.le
      _ = v / 150 := by ring
  have hx6 : ‖x‖ ≤ 1 / 6 := by linarith
  have hone : ‖1 - x‖ ≤ 1 := by
    have heq : 1 - x = (1 + (v : ℂ) * xiZeroCopyReciprocalSquare q)⁻¹ := by
      dsimp [x, xiShiftedReciprocalSquare]
      have hd : 1 + xiZeroCopyReciprocalSquare q * (v : ℂ) ≠ 0 := by
        simpa only [mul_comm] using one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hv.le q
      field_simp [one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hv.le q, hd]
      ring
    rw [heq, norm_inv]
    have hd := one_le_norm_one_add_mul_xiZeroCopyReciprocalSquare hv.le q
    exact (inv_le_one₀ (by linarith)).mpr hd
  have hclock : 16 * ((n + 1 : ℕ) : ℝ) ^ 2 * ‖x‖ ≤ 8 / 3 := by
    have hh := mul_le_mul_of_nonneg_left hx
      (show 0 ≤ 16 * ((n + 1 : ℕ) : ℝ) ^ 2 by positivity)
    nlinarith
  have hpoly := normalizedEndpointPolynomial_error_le n x hclock
  have hradial : ‖(1 - x) ^ 2 - 1‖ ≤ 13 / 36 := by
    have heq : (1 - x) ^ 2 - 1 = -(2 * x) + x ^ 2 := by ring
    have hs := pow_le_pow_left₀ (norm_nonneg x) hx6 2
    calc
      ‖(1 - x) ^ 2 - 1‖ ≤ 2 * ‖x‖ + ‖x‖ ^ 2 := by
        rw [heq]
        have hh := norm_add_le (-(2 * x)) (x ^ (2 : ℕ))
        simpa only [norm_neg, norm_mul, norm_ofNat, norm_pow] using hh
      _ ≤ 13 / 36 := by nlinarith
  have hinner : ‖(1 - x) ^ 2 *
      evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1‖ ≤ 409 / 468 := by
    have heq : (1 - x) ^ 2 * evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1 =
        ((1 - x) ^ 2 - 1) + (1 - x) ^ 2 *
          (evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1) := by ring
    have hradnorm : ‖(1 - x) ^ 2‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hone
    rw [heq]
    calc
      ‖((1 - x) ^ 2 - 1) + (1 - x) ^ 2 *
          (evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1)‖ ≤
          ‖(1 - x) ^ 2 - 1‖ + ‖(1 - x) ^ 2‖ *
            ‖evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1‖ := by
        have hh : ‖((1 - x) ^ 2 - 1) + (1 - x) ^ 2 *
            (evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1)‖ ≤
            ‖(1 - x) ^ 2 - 1‖ + ‖(1 - x) ^ 2 *
              (evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1)‖ :=
          norm_add_le _ _
        rw [_root_.norm_mul] at hh
        exact hh
      _ ≤ 13 / 36 + 1 * (20 / 39) := add_le_add hradial
        (mul_le_mul hradnorm hpoly (norm_nonneg _) zero_le_one)
      _ = 409 / 468 := by norm_num
  rw [liEvenCrossSquareMassAdjacentFlux_div_eq_normalizedEndpointPolynomial hv]
  change ‖xiZeroCopyReciprocalSquare q * (1 - x) ^ 2 *
      evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - xiZeroCopyReciprocalSquare q‖ ≤ _
  rw [show xiZeroCopyReciprocalSquare q * (1 - x) ^ 2 *
      evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - xiZeroCopyReciprocalSquare q =
      xiZeroCopyReciprocalSquare q * ((1 - x) ^ 2 *
        evalRealPolynomial (liEvenCrossNormalizedEndpointPolynomial n) x - 1) by ring, norm_mul]
  exact (mul_le_mul_of_nonneg_left hinner (norm_nonneg _)).trans_eq (by ring)

private theorem normalized_actual_current_error_le
    {v : ℝ} (hv : 0 < v) (n : ℕ)
    (hwindow : ((n + 1 : ℕ) : ℝ) ^ 2 * v ≤ 25) :
    |liEvenCrossSquareMassAdjacentCurrent v n /
        (2 * ((n + 1 : ℕ) : ℝ) ^ 2) - normalizedPrimeArchMoment 0| ≤
      (409 / 468 : ℝ) * xiShiftAbsoluteMass 0 := by
  let c : ℝ := 1 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)
  let f : XiZeroCopy → ℂ := fun q => (c : ℂ) * liEvenCrossSquareMassAdjacentFlux v n q
  have hf : Summable f := (summable_liEvenCrossSquareMassAdjacentFlux hv n).mul_left (c : ℂ)
  have hl : Summable xiZeroCopyReciprocalSquare := by
    simpa only [zero_add, pow_one] using summable_xiZeroCopyReciprocalSquare_pow 0
  have ha : Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
    simpa only [zero_add, pow_one] using summable_xiShiftAbsoluteMass 0
  have hpoint (q : XiZeroCopy) : ‖f q - xiZeroCopyReciprocalSquare q‖ ≤
      (409 / 468 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ := by
    simpa [f, c, div_eq_mul_inv, mul_comm] using actual_current_atom_error_le hv n hwindow q
  have hsum : ‖∑' q : XiZeroCopy, (f q - xiZeroCopyReciprocalSquare q)‖ ≤
      (409 / 468 : ℝ) * xiShiftAbsoluteMass 0 := by
    calc
      ‖∑' q : XiZeroCopy, (f q - xiZeroCopyReciprocalSquare q)‖ ≤
          ∑' q : XiZeroCopy, ‖f q - xiZeroCopyReciprocalSquare q‖ :=
        norm_tsum_le_tsum_norm (hf.sub hl).norm
      _ ≤ ∑' q : XiZeroCopy, (409 / 468 : ℝ) * ‖xiZeroCopyReciprocalSquare q‖ :=
        (hf.sub hl).norm.tsum_le_tsum hpoint (ha.mul_left _)
      _ = (409 / 468 : ℝ) * xiShiftAbsoluteMass 0 := by
        rw [tsum_mul_left]
        simp [xiShiftAbsoluteMass]
  have hf_re : (∑' q : XiZeroCopy, f q).re =
      liEvenCrossSquareMassAdjacentCurrent v n / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [f]
    rw [tsum_mul_left, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← liEvenCrossSquareMassAdjacentCurrent_eq_re_tsum hv n]
    dsimp [c]
    ring
  have hm : (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q).re = normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment]
    simpa only [zero_add, pow_one] using congrArg Complex.re (tsum_xiZeroCopyReciprocalSquare_pow 0)
  have heq : (∑' q : XiZeroCopy, (f q - xiZeroCopyReciprocalSquare q)).re =
      liEvenCrossSquareMassAdjacentCurrent v n / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) -
        normalizedPrimeArchMoment 0 := by
    rw [hf.tsum_sub hl, Complex.sub_re, hf_re, hm]
  rw [← heq]
  exact (Complex.abs_re_le_norm _).trans hsum

/-- Uniform quantitative lower bound for the complete actual current. -/
theorem liEvenCrossSquareMassAdjacentCurrent_normalized_lower_of_degree_sq_mul_le_twentyFive
    {v : ℝ} (hv : 0 < v) (n : ℕ)
    (hwindow : ((n + 1 : ℕ) : ℝ) ^ 2 * v ≤ 25) :
    (787 / 6552 : ℝ) * xiShiftAbsoluteMass 0 ≤
      liEvenCrossSquareMassAdjacentCurrent v n / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have he := (abs_le.mp (normalized_actual_current_error_le hv n hwindow)).1
  have hs := sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 0
  norm_num at hs
  linarith

/-- A positive prefix whose length grows like the inverse square root of mass. -/
theorem liEvenCrossSquareMassAdjacentCurrent_pos_of_degree_sq_mul_le_twentyFive
    {v : ℝ} (hv : 0 < v) (n : ℕ)
    (hwindow : ((n + 1 : ℕ) : ℝ) ^ 2 * v ≤ 25) :
    0 < liEvenCrossSquareMassAdjacentCurrent v n := by
  have hl := liEvenCrossSquareMassAdjacentCurrent_normalized_lower_of_degree_sq_mul_le_twentyFive
    hv n hwindow
  have ha := xiShiftAbsoluteMass_pos 0
  have hp : 0 < liEvenCrossSquareMassAdjacentCurrent v n /
      (2 * ((n + 1 : ℕ) : ℝ) ^ 2) := lt_of_lt_of_le (by positivity) hl
  have hd : 0 < 2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hm := mul_pos hp hd
  simpa only [div_mul_cancel₀ _ (ne_of_gt hd)] using hm

/-- Every positive-mass current zero lies outside the certified window. -/
theorem degree_sq_mul_gt_twentyFive_of_liEvenCrossSquareMassAdjacentCurrent_zero
    {v : ℝ} (hv : 0 < v) (n : ℕ)
    (hzero : liEvenCrossSquareMassAdjacentCurrent v n = 0) :
    25 < ((n + 1 : ℕ) : ℝ) ^ 2 * v := by
  by_contra hnot
  exact (ne_of_gt (liEvenCrossSquareMassAdjacentCurrent_pos_of_degree_sq_mul_le_twentyFive
    hv n (le_of_not_gt hnot))) hzero

/-- All modes through nine are positive on the complete interior mass window. -/
theorem liEvenCrossSquareMassAdjacentCurrent_pos_of_le_nine
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) {n : ℕ} (hn : n ≤ 9) :
    0 < liEvenCrossSquareMassAdjacentCurrent v n := by
  have hn10 : ((n + 1 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (show n + 1 ≤ 10 by omega)
  have hs : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 100 := by
    have hnon : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  apply liEvenCrossSquareMassAdjacentCurrent_pos_of_degree_sq_mul_le_twentyFive hv n
  calc
    ((n + 1 : ℕ) : ℝ) ^ 2 * v ≤ 100 * v := mul_le_mul_of_nonneg_right hs hv.le
    _ ≤ 25 := by linarith

end
end RHTower
