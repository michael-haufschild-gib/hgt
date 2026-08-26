import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomWardObstructionScaleQuadrature
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# High-order rational quadrature for the first theta atom

A ninth-order local exponential enclosure on the fixed `1/64` mesh removes the first-order
chord loss in the earlier quadrature.  One polynomial certificate simultaneously encloses the
first four raw even moments tightly enough for centered order 24.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- Taylor polynomial for `exp (2y)` through degree eight. -/
def thetaCuspExpTwoTaylorEightPolynomial : ℝ[X] :=
  1 + C 2 * X + C 2 * X ^ 2 + C (4 / 3) * X ^ 3 +
    C (2 / 3) * X ^ 4 + C (4 / 15) * X ^ 5 +
    C (4 / 45) * X ^ 6 + C (8 / 315) * X ^ 7 + C (2 / 315) * X ^ 8

/-- The factorial remainder with `exp (2y) < 3` inserted. -/
def thetaCuspExpTwoTaylorEightUpperPolynomial : ℝ[X] :=
  thetaCuspExpTwoTaylorEightPolynomial + C (4 / 945) * X ^ 9

def thetaCuspThirtySecondExpTaylorLower : ℝ :=
  thetaCuspExpTwoTaylorEightPolynomial.eval (1 / 64)

def thetaCuspThirtySecondExpTaylorUpper : ℝ :=
  thetaCuspExpTwoTaylorEightUpperPolynomial.eval (1 / 64)

theorem thetaCuspExpTwoTaylorEightPolynomial_eval (y : ℝ) :
    thetaCuspExpTwoTaylorEightPolynomial.eval y =
      1 + 2 * y + 2 * y ^ 2 + (4 / 3) * y ^ 3 +
        (2 / 3) * y ^ 4 + (4 / 15) * y ^ 5 +
        (4 / 45) * y ^ 6 + (8 / 315) * y ^ 7 + (2 / 315) * y ^ 8 := by
  simp [thetaCuspExpTwoTaylorEightPolynomial]

theorem thetaCuspExpTwoTaylorEightUpperPolynomial_eval (y : ℝ) :
    thetaCuspExpTwoTaylorEightUpperPolynomial.eval y =
      thetaCuspExpTwoTaylorEightPolynomial.eval y + (4 / 945) * y ^ 9 := by
  simp [thetaCuspExpTwoTaylorEightUpperPolynomial]

theorem thetaCuspExpTwoTaylorEightPolynomial_le_exp
    {y : ℝ} (hy : 0 ≤ y) :
    thetaCuspExpTwoTaylorEightPolynomial.eval y ≤ Real.exp (2 * y) := by
  have h := Real.sum_le_exp_of_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hy) 9
  norm_num [Finset.sum_range_succ] at h
  rw [thetaCuspExpTwoTaylorEightPolynomial_eval]
  nlinarith

theorem exp_le_thetaCuspExpTwoTaylorEightUpperPolynomial
    {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    Real.exp (2 * y) ≤ thetaCuspExpTwoTaylorEightUpperPolynomial.eval y := by
  have hr : 0 ≤ 2 * y := mul_nonneg (by norm_num) hy
  have hrem := real_exp_sub_sum_le_factorial_tail (2 * y) hr 9
  norm_num [Finset.sum_range_succ] at hrem
  have harg : 2 * y ≤ 1 := by nlinarith
  have hexp : Real.exp (2 * y) < 3 := by
    exact (Real.exp_le_exp.mpr harg).trans_lt
      (Real.exp_one_lt_d9.trans (by norm_num))
  have hpow : 0 ≤ (2 * y) ^ 9 / (Nat.factorial 9 : ℝ) := by positivity
  have htail :
      ((2 * y) ^ 9 / (Nat.factorial 9 : ℝ)) * Real.exp (2 * y) ≤
        ((2 * y) ^ 9 / (Nat.factorial 9 : ℝ)) * 3 :=
    mul_le_mul_of_nonneg_left hexp.le hpow
  rw [thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
    thetaCuspExpTwoTaylorEightPolynomial_eval]
  norm_num at htail ⊢
  nlinarith

theorem thetaCuspThirtySecondExpTaylorLower_le_exp :
    thetaCuspThirtySecondExpTaylorLower ≤ Real.exp (1 / 32 : ℝ) := by
  rw [thetaCuspThirtySecondExpTaylorLower]
  convert thetaCuspExpTwoTaylorEightPolynomial_le_exp
    (y := (1 / 64 : ℝ)) (by norm_num) using 1 <;> norm_num

theorem exp_le_thetaCuspThirtySecondExpTaylorUpper :
    Real.exp (1 / 32 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
  rw [thetaCuspThirtySecondExpTaylorUpper]
  convert exp_le_thetaCuspExpTwoTaylorEightUpperPolynomial
    (y := (1 / 64 : ℝ)) (by norm_num) (by norm_num) using 1 <;> norm_num

theorem thetaCuspThirtySecondExpTaylorLower_pow_le_exp (j : ℕ) :
    thetaCuspThirtySecondExpTaylorLower ^ j ≤ Real.exp ((j : ℝ) / 32) := by
  rw [show (j : ℝ) / 32 = (j : ℕ) * (1 / 32 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial, eval_add, eval_mul, eval_pow])
    thetaCuspThirtySecondExpTaylorLower_le_exp j

theorem exp_le_thetaCuspThirtySecondExpTaylorUpper_pow (j : ℕ) :
    Real.exp ((j : ℝ) / 32) ≤ thetaCuspThirtySecondExpTaylorUpper ^ j := by
  rw [show (j : ℝ) / 32 = (j : ℕ) * (1 / 32 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le
    exp_le_thetaCuspThirtySecondExpTaylorUpper j

def thetaCuspFirstRateTaylorUpperEndpoint64 (j : ℕ) : ℝ :=
  (3.14159265358979323847 : ℝ) *
      (thetaCuspThirtySecondExpTaylorUpper ^ j - 1) - 5 * ((j : ℝ) / 64) / 2

def thetaCuspFirstRateTaylorLowerEndpoint64 (j : ℕ) : ℝ :=
  (3.14159265358979323846 : ℝ) *
      (thetaCuspThirtySecondExpTaylorLower ^ j - 1) - 5 * ((j : ℝ) / 64) / 2

def thetaCuspFirstRateTaylorUpperDelta64 (j : ℕ) : ℝ[X] :=
  C ((3.14159265358979323847 : ℝ) * thetaCuspThirtySecondExpTaylorUpper ^ j) *
      (thetaCuspExpTwoTaylorEightUpperPolynomial - 1) - C (5 / 2) * X

def thetaCuspFirstRateTaylorLowerDelta64 (j : ℕ) : ℝ[X] :=
  C ((3.14159265358979323846 : ℝ) * thetaCuspThirtySecondExpTaylorLower ^ j) *
      (thetaCuspExpTwoTaylorEightPolynomial - 1) - C (5 / 2) * X

theorem thetaCuspFirstLiouvilleRate_taylor_bounds64
    {j : ℕ} {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    thetaCuspFirstRateTaylorLowerEndpoint64 j +
        (thetaCuspFirstRateTaylorLowerDelta64 j).eval y ≤
      thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y) ∧
    thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y) ≤
      thetaCuspFirstRateTaylorUpperEndpoint64 j +
        (thetaCuspFirstRateTaylorUpperDelta64 j).eval y := by
  have hlocalLower := thetaCuspExpTwoTaylorEightPolynomial_le_exp hy
  have hlocalUpper := exp_le_thetaCuspExpTwoTaylorEightUpperPolynomial hy hyh
  have hgridLower := thetaCuspThirtySecondExpTaylorLower_pow_le_exp j
  have hgridUpper := exp_le_thetaCuspThirtySecondExpTaylorUpper_pow j
  have hTl0 : 0 ≤ thetaCuspExpTwoTaylorEightPolynomial.eval y := by
    rw [thetaCuspExpTwoTaylorEightPolynomial_eval]
    positivity
  have hTu0 : 0 ≤ thetaCuspExpTwoTaylorEightUpperPolynomial.eval y := by
    exact (Real.exp_pos _).le.trans hlocalUpper
  have hbaseLowerOne : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorLower := by
    norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hgridLowerOne : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorLower ^ j :=
    one_le_pow₀ hbaseLowerOne
  have hTl1 : (1 : ℝ) ≤ thetaCuspExpTwoTaylorEightPolynomial.eval y := by
    rw [thetaCuspExpTwoTaylorEightPolynomial_eval]
    nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4,
      pow_nonneg hy 5, pow_nonneg hy 6, pow_nonneg hy 7, pow_nonneg hy 8]
  have hfactor : Real.exp (2 * ((j : ℝ) / 64 + y)) =
      Real.exp ((j : ℝ) / 32) * Real.exp (2 * y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpLower :
      thetaCuspThirtySecondExpTaylorLower ^ j *
          thetaCuspExpTwoTaylorEightPolynomial.eval y ≤
        Real.exp (2 * ((j : ℝ) / 64 + y)) := by
    rw [hfactor]
    exact mul_le_mul hgridLower hlocalLower hTl0 (Real.exp_pos _).le
  have hexpUpper :
      Real.exp (2 * ((j : ℝ) / 64 + y)) ≤
        thetaCuspThirtySecondExpTaylorUpper ^ j *
          thetaCuspExpTwoTaylorEightUpperPolynomial.eval y := by
    rw [hfactor]
    exact mul_le_mul hgridUpper hlocalUpper (Real.exp_pos _).le
      (pow_nonneg (by norm_num [thetaCuspThirtySecondExpTaylorUpper,
        thetaCuspExpTwoTaylorEightUpperPolynomial,
        thetaCuspExpTwoTaylorEightPolynomial]) _)
  have hlowerProductOne : (1 : ℝ) ≤
      thetaCuspThirtySecondExpTaylorLower ^ j *
        thetaCuspExpTwoTaylorEightPolynomial.eval y := by
    nlinarith [mul_le_mul hgridLowerOne hTl1 (by norm_num : (0 : ℝ) ≤ 1)
      (pow_nonneg (by norm_num [thetaCuspThirtySecondExpTaylorLower,
        thetaCuspExpTwoTaylorEightPolynomial]) j)]
  have hactualOne : (1 : ℝ) ≤ Real.exp (2 * ((j : ℝ) / 64 + y)) := by
    apply Real.one_le_exp
    positivity
  constructor
  · rw [thetaCuspFirstLiouvilleRate,
      thetaCuspFirstRateTaylorLowerEndpoint64,
      thetaCuspFirstRateTaylorLowerDelta64]
    simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X]
    have hpi := Real.pi_gt_d20.le
    have hweighted := mul_le_mul hpi
      (sub_le_sub_right hexpLower 1)
      (sub_nonneg.mpr hlowerProductOne) Real.pi_pos.le
    linarith
  · rw [thetaCuspFirstLiouvilleRate,
      thetaCuspFirstRateTaylorUpperEndpoint64,
      thetaCuspFirstRateTaylorUpperDelta64]
    simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X]
    have hpi := Real.pi_lt_d20.le
    have hweighted := mul_le_mul hpi
      (sub_le_sub_right hexpUpper 1)
      (sub_nonneg.mpr hactualOne) (by norm_num)
    linarith

def thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 (j : ℕ) : ℝ :=
  (expNegTruncPoly 64).eval (thetaCuspFirstRateTaylorUpperEndpoint64 j)

def thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 (j : ℕ) : ℝ :=
  (expNegTruncPoly 65).eval (thetaCuspFirstRateTaylorLowerEndpoint64 j)

def thetaCuspFirstRateTaylorLocalLowerCertificate64 (j : ℕ) : ℝ[X] :=
  (expNegTruncPoly 10).comp (thetaCuspFirstRateTaylorUpperDelta64 j)

def thetaCuspFirstRateTaylorLocalUpperCertificate64 (j : ℕ) : ℝ[X] :=
  (expNegTruncPoly 9).comp (thetaCuspFirstRateTaylorLowerDelta64 j)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem thetaCuspFirstRateTaylorUpperEndpoint64_nonneg
    {j : ℕ} (hj : j < 64) :
    0 ≤ thetaCuspFirstRateTaylorUpperEndpoint64 j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstRateTaylorUpperEndpoint64,
      thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem thetaCuspFirstRateTaylorLowerEndpoint64_nonneg
    {j : ℕ} (hj : j < 64) :
    0 ≤ thetaCuspFirstRateTaylorLowerEndpoint64 j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstRateTaylorLowerEndpoint64,
      thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_pos
    {j : ℕ} (hj : j < 64) :
    0 < thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64,
      thetaCuspFirstRateTaylorUpperEndpoint64,
      thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial,
      eval_expNegTruncPoly, Finset.sum_range_succ]

theorem thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_le_exp
    {j : ℕ} (hj : j < 64) :
    thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j ≤
      Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) := by
  have hz := thetaCuspFirstRateTaylorUpperEndpoint64_nonneg hj
  rcases hz.eq_or_lt with hz0 | hzpos
  · rw [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64, ← hz0]
    norm_num [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64,
      eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 64) (by norm_num) hzpos
    norm_num at h
    simpa only [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64] using h.le

theorem exp_le_thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64
    {j : ℕ} (hj : j < 64) :
    Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 j) ≤
      thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j := by
  have hz := thetaCuspFirstRateTaylorLowerEndpoint64_nonneg hj
  rcases hz.eq_or_lt with hz0 | hzpos
  · rw [thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64, ← hz0]
    norm_num [thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64,
      eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 65) (by norm_num) hzpos
    norm_num at h
    simpa only [thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64] using h.le

theorem thetaCuspFirstRateTaylorLowerDelta64_eval_nonneg
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ (thetaCuspFirstRateTaylorLowerDelta64 j).eval y := by
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorLower := by
    norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorLower ^ j :=
    one_le_pow₀ hbase
  rw [thetaCuspFirstRateTaylorLowerDelta64]
  simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X]
  rw [thetaCuspExpTwoTaylorEightPolynomial_eval]
  nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4,
    pow_nonneg hy 5, pow_nonneg hy 6, pow_nonneg hy 7, pow_nonneg hy 8]

theorem thetaCuspFirstRateTaylorUpperDelta64_eval_nonneg
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ (thetaCuspFirstRateTaylorUpperDelta64 j).eval y := by
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper ^ j :=
    one_le_pow₀ hbase
  rw [thetaCuspFirstRateTaylorUpperDelta64]
  simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X]
  rw [thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
    thetaCuspExpTwoTaylorEightPolynomial_eval]
  nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4,
    pow_nonneg hy 5, pow_nonneg hy 6, pow_nonneg hy 7, pow_nonneg hy 8,
    pow_nonneg hy 9]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
theorem thetaCuspFirstRateTaylorUpperDelta64_eval_le_one
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (thetaCuspFirstRateTaylorUpperDelta64 j).eval y ≤ 1 := by
  have h2 := pow_le_pow_left₀ hy hyh 2
  have h3 := pow_le_pow_left₀ hy hyh 3
  have h4 := pow_le_pow_left₀ hy hyh 4
  have h5 := pow_le_pow_left₀ hy hyh 5
  have h6 := pow_le_pow_left₀ hy hyh 6
  have h7 := pow_le_pow_left₀ hy hyh 7
  have h8 := pow_le_pow_left₀ hy hyh 8
  have h9 := pow_le_pow_left₀ hy hyh 9
  interval_cases j <;>
    norm_num [thetaCuspFirstRateTaylorUpperDelta64,
      thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial] at * <;>
    nlinarith

theorem expNegTruncPoly_ten_eval_pos_of_mem_unit
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (expNegTruncPoly 10).eval t := by
  have hid : (expNegTruncPoly 10).eval t =
      (1 - t) + t ^ 2 * (3 - t) / 6 + t ^ 4 * (5 - t) / 120 +
        t ^ 6 * (7 - t) / 5040 + t ^ 8 * (9 - t) / 362880 := by
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
    ring
  rw [hid]
  rcases ht0.eq_or_lt with rfl | htpos
  · norm_num
  · have hfirst : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsecond : 0 < t ^ 2 * (3 - t) / 6 := by
      exact div_pos (mul_pos (sq_pos_of_pos htpos) (by linarith)) (by norm_num)
    have hfourth : 0 ≤ t ^ 4 * (5 - t) / 120 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 4) (by linarith)) (by norm_num)
    have hsixth : 0 ≤ t ^ 6 * (7 - t) / 5040 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 6) (by linarith)) (by norm_num)
    have heighth : 0 ≤ t ^ 8 * (9 - t) / 362880 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 8) (by linarith)) (by norm_num)
    linarith

theorem thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_pos
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    0 < (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y := by
  rw [thetaCuspFirstRateTaylorLocalLowerCertificate64, eval_comp]
  exact expNegTruncPoly_ten_eval_pos_of_mem_unit
    (thetaCuspFirstRateTaylorUpperDelta64_eval_nonneg j hy)
    (thetaCuspFirstRateTaylorUpperDelta64_eval_le_one hj hy hyh)

theorem thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_le_exp
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y ≤
      Real.exp (-(thetaCuspFirstRateTaylorUpperDelta64 j).eval y) := by
  let t := (thetaCuspFirstRateTaylorUpperDelta64 j).eval y
  have ht0 : 0 ≤ t := thetaCuspFirstRateTaylorUpperDelta64_eval_nonneg j hy
  rw [thetaCuspFirstRateTaylorLocalLowerCertificate64, eval_comp]
  change (expNegTruncPoly 10).eval t ≤ Real.exp (-t)
  rcases ht0.eq_or_lt with htzero | htpos
  · rw [← htzero]
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 10) (by norm_num) htpos
    norm_num at h
    exact h.le

theorem exp_le_thetaCuspFirstRateTaylorLocalUpperCertificate64_eval
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y) ≤
      (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by
  rw [thetaCuspFirstRateTaylorLocalUpperCertificate64, eval_comp]
  exact exp_neg_le_expNegTruncPoly_nine
    (thetaCuspFirstRateTaylorLowerDelta64_eval_nonneg j hy)

def thetaCuspFirstSourceTaylorLower64 (j : ℕ) : ℝ[X] :=
  C ((6.28318530717958647692 : ℝ) *
      thetaCuspThirtySecondExpTaylorLower ^ j) *
    thetaCuspExpTwoTaylorEightPolynomial - C 3

def thetaCuspFirstSourceTaylorUpper64 (j : ℕ) : ℝ[X] :=
  C ((6.28318530717958647694 : ℝ) *
      thetaCuspThirtySecondExpTaylorUpper ^ j) *
    thetaCuspExpTwoTaylorEightUpperPolynomial - C 3

theorem thetaCuspFirstSourceTaylorLower64_eval_nonneg
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ (thetaCuspFirstSourceTaylorLower64 j).eval y := by
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorLower := by
    norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorLower ^ j :=
    one_le_pow₀ hbase
  rw [thetaCuspFirstSourceTaylorLower64]
  simp only [eval_sub, eval_mul, eval_C]
  rw [thetaCuspExpTwoTaylorEightPolynomial_eval]
  nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4,
    pow_nonneg hy 5, pow_nonneg hy 6, pow_nonneg hy 7, pow_nonneg hy 8]

theorem thetaCuspFirstSourceTaylorLower64_eval_le_actual
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (thetaCuspFirstSourceTaylorLower64 j).eval y ≤
      2 * Real.pi * Real.exp (2 * ((j : ℝ) / 64 + y)) - 3 := by
  have hlocal := thetaCuspExpTwoTaylorEightPolynomial_le_exp hy
  have hgrid := thetaCuspThirtySecondExpTaylorLower_pow_le_exp j
  have hT0 : 0 ≤ thetaCuspExpTwoTaylorEightPolynomial.eval y := by
    rw [thetaCuspExpTwoTaylorEightPolynomial_eval]
    positivity
  have hproduct :
      thetaCuspThirtySecondExpTaylorLower ^ j *
          thetaCuspExpTwoTaylorEightPolynomial.eval y ≤
        Real.exp (2 * ((j : ℝ) / 64 + y)) := by
    rw [show 2 * ((j : ℝ) / 64 + y) = (j : ℝ) / 32 + 2 * y by ring,
      Real.exp_add]
    exact mul_le_mul hgrid hlocal hT0 (Real.exp_pos _).le
  have hpi : (6.28318530717958647692 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_d20]
  rw [thetaCuspFirstSourceTaylorLower64]
  simp only [eval_sub, eval_mul, eval_C]
  calc
    (6.28318530717958647692 : ℝ) *
          (thetaCuspThirtySecondExpTaylorLower ^ j *
            thetaCuspExpTwoTaylorEightPolynomial.eval y) - 3 ≤
        (6.28318530717958647692 : ℝ) *
          Real.exp (2 * ((j : ℝ) / 64 + y)) - 3 := by gcongr
    _ ≤ 2 * Real.pi * Real.exp (2 * ((j : ℝ) / 64 + y)) - 3 := by
      gcongr

theorem actual_le_thetaCuspFirstSourceTaylorUpper64_eval
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    2 * Real.pi * Real.exp (2 * ((j : ℝ) / 64 + y)) - 3 ≤
      (thetaCuspFirstSourceTaylorUpper64 j).eval y := by
  have hlocal := exp_le_thetaCuspExpTwoTaylorEightUpperPolynomial hy hyh
  have hgrid := exp_le_thetaCuspThirtySecondExpTaylorUpper_pow j
  have hproduct : Real.exp (2 * ((j : ℝ) / 64 + y)) ≤
      thetaCuspThirtySecondExpTaylorUpper ^ j *
        thetaCuspExpTwoTaylorEightUpperPolynomial.eval y := by
    rw [show 2 * ((j : ℝ) / 64 + y) = (j : ℝ) / 32 + 2 * y by ring,
      Real.exp_add]
    exact mul_le_mul hgrid hlocal (Real.exp_pos _).le
      (pow_nonneg (by norm_num [thetaCuspThirtySecondExpTaylorUpper,
        thetaCuspExpTwoTaylorEightUpperPolynomial,
        thetaCuspExpTwoTaylorEightPolynomial]) _)
  have hpi : 2 * Real.pi ≤ (6.28318530717958647694 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  have hupper0 : 0 ≤ thetaCuspThirtySecondExpTaylorUpper ^ j *
      thetaCuspExpTwoTaylorEightUpperPolynomial.eval y := by positivity
  rw [thetaCuspFirstSourceTaylorUpper64]
  simp only [eval_sub, eval_mul, eval_C]
  calc
    2 * Real.pi * Real.exp (2 * ((j : ℝ) / 64 + y)) - 3 ≤
        2 * Real.pi * (thetaCuspThirtySecondExpTaylorUpper ^ j *
          thetaCuspExpTwoTaylorEightUpperPolynomial.eval y) - 3 := by gcongr
    _ ≤ (6.28318530717958647694 : ℝ) *
          (thetaCuspThirtySecondExpTaylorUpper ^ j *
            thetaCuspExpTwoTaylorEightUpperPolynomial.eval y) - 3 := by
      gcongr

theorem thetaCuspFirstGibbsTaylorLower64_le
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y ≤
      thetaCuspLiouvilleGibbsAtom 1 ((j : ℝ) / 64 + y) := by
  have hrate := (thetaCuspFirstLiouvilleRate_taylor_bounds64 hy hyh).2
  have hendpoint :=
    thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_le_exp hj
  have hlocal :=
    thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_le_exp hj hy hyh
  have hendpoint0 :=
    (thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_pos hj).le
  have hlocal0 :=
    (thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_pos hj hy hyh).le
  rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    (0.0432139182637 : ℝ) *
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
          (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y ≤
        Real.exp (-Real.pi) *
          (thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
            (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y) := by
      exact mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_lower
        (mul_nonneg hendpoint0 hlocal0)
    _ ≤ Real.exp (-Real.pi) *
          (Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) *
            Real.exp (-(thetaCuspFirstRateTaylorUpperDelta64 j).eval y)) := by
      gcongr
    _ = Real.exp (-Real.pi) *
          Real.exp (-(thetaCuspFirstRateTaylorUpperEndpoint64 j +
            (thetaCuspFirstRateTaylorUpperDelta64 j).eval y)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-Real.pi) *
          Real.exp (-thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y)) := by
      gcongr

theorem thetaCuspFirstGibbs_le_taylorUpper64
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    thetaCuspLiouvilleGibbsAtom 1 ((j : ℝ) / 64 + y) ≤
      (0.0432139182638 : ℝ) *
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
        (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by
  have hrate := (thetaCuspFirstLiouvilleRate_taylor_bounds64 hy hyh).1
  have hendpoint :=
    exp_le_thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 hj
  have hlocal := exp_le_thetaCuspFirstRateTaylorLocalUpperCertificate64_eval j hy
  rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    Real.exp (-Real.pi) *
          Real.exp (-thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y)) ≤
        Real.exp (-Real.pi) *
          Real.exp (-(thetaCuspFirstRateTaylorLowerEndpoint64 j +
            (thetaCuspFirstRateTaylorLowerDelta64 j).eval y)) := by
      gcongr
    _ = Real.exp (-Real.pi) *
          (Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 j) *
            Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y)) := by
      rw [← Real.exp_add]
    _ ≤ (0.0432139182638 : ℝ) *
          (Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 j) *
            Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y)) := by
      exact mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_upper
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ ≤ (0.0432139182638 : ℝ) *
          thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
          (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by
      positivity

end

end RHTower
