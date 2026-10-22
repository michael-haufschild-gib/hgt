import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomWardObstructionScaleQuadrature
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy

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
  1 + C 2 * X + C 2 * X ^ (2 : ℕ) + C (4 / 3) * X ^ (3 : ℕ) +
    C (2 / 3) * X ^ (4 : ℕ) + C (4 / 15) * X ^ (5 : ℕ) +
    C (4 / 45) * X ^ (6 : ℕ) + C (8 / 315) * X ^ (7 : ℕ) + C (2 / 315) * X ^ (8 : ℕ)

/-- The factorial remainder with `exp (2y) < 3` inserted. -/
def thetaCuspExpTwoTaylorEightUpperPolynomial : ℝ[X] :=
  thetaCuspExpTwoTaylorEightPolynomial + C (4 / 945) * X ^ (9 : ℕ)

def thetaCuspThirtySecondExpTaylorLower : ℝ :=
  thetaCuspExpTwoTaylorEightPolynomial.eval (1 / 64)

def thetaCuspThirtySecondExpTaylorUpper : ℝ :=
  thetaCuspExpTwoTaylorEightUpperPolynomial.eval (1 / 64)

namespace ThetaRationalQuadrature

abbrev QPoly := List ℚ

def coeff (p : QPoly) (n : ℕ) : ℚ := p[n]?.getD 0

def add : QPoly → QPoly → QPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def neg (p : QPoly) : QPoly := p.map (-·)
def sub (p q : QPoly) : QPoly := add p (neg q)
def scale (a : ℚ) (p : QPoly) : QPoly := p.map (a * ·)

def mul : QPoly → QPoly → QPoly
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def pow (p : QPoly) : ℕ → QPoly
  | 0 => [1]
  | n + 1 => mul (pow p n) p

def comp (p q : QPoly) : QPoly :=
  p.foldr (fun a acc => add [a] (mul q acc)) []

def eval (p : QPoly) (x : ℚ) : ℚ :=
  p.foldr (fun a acc => a + x * acc) 0

def C (a : ℚ) : QPoly := [a]
def X : QPoly := [0, 1]

def expTwoTaylor : QPoly :=
  [1, 2, 2, 4 / 3, 2 / 3, 4 / 15, 4 / 45, 8 / 315, 2 / 315]

def expTwoTaylorUpper : QPoly :=
  add expTwoTaylor (mul (C (4 / 945)) (pow X 9))

def thirtySecondExpLower : ℚ := eval expTwoTaylor (1 / 64)
def thirtySecondExpUpper : ℚ := eval expTwoTaylorUpper (1 / 64)

def expNeg (P : ℕ) : QPoly :=
  List.ofFn fun p : Fin P => ((-1 : ℚ) ^ (p : ℕ)) / ((p : ℕ).factorial : ℚ)

def upperIncrement (j : ℕ) : ℚ :=
  (3.14159265358979323847 : ℚ) * thirtySecondExpUpper ^ j *
      (thirtySecondExpUpper - 1) - 5 / 128

def lowerIncrement (j : ℕ) : ℚ :=
  (3.14159265358979323846 : ℚ) * thirtySecondExpLower ^ j *
      (thirtySecondExpLower - 1) - 5 / 128

def roundDown (x : ℚ) : ℚ :=
  ((x * 1000000000000).floor : ℚ) / 1000000000000

def roundUp (x : ℚ) : ℚ :=
  ((x * 1000000000000).ceil : ℚ) / 1000000000000

def endpointLower : ℕ → ℚ
  | 0 => 1
  | j + 1 => roundDown (endpointLower j * eval (expNeg 10) (upperIncrement j))

def endpointUpper : ℕ → ℚ
  | 0 => 1
  | j + 1 => roundUp (endpointUpper j * eval (expNeg 9) (lowerIncrement j))

end ThetaRationalQuadrature

theorem thetaCuspExpTwoTaylorEightPolynomial_eval (y : ℝ) :
    thetaCuspExpTwoTaylorEightPolynomial.eval y =
      1 + 2 * y + 2 * y ^ (2 : ℕ) + (4 / 3) * y ^ (3 : ℕ) +
        (2 / 3) * y ^ (4 : ℕ) + (4 / 15) * y ^ (5 : ℕ) +
        (4 / 45) * y ^ (6 : ℕ) + (8 / 315) * y ^ (7 : ℕ) + (2 / 315) * y ^ (8 : ℕ) := by
  simp [thetaCuspExpTwoTaylorEightPolynomial]

theorem thetaCuspExpTwoTaylorEightUpperPolynomial_eval (y : ℝ) :
    thetaCuspExpTwoTaylorEightUpperPolynomial.eval y =
      thetaCuspExpTwoTaylorEightPolynomial.eval y + (4 / 945) * y ^ (9 : ℕ) := by
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
  have hpow : 0 ≤ (2 * y) ^ (9 : ℕ) / (Nat.factorial 9 : ℝ) := by positivity
  have htail :
      ((2 * y) ^ (9 : ℕ) / (Nat.factorial 9 : ℝ)) * Real.exp (2 * y) ≤
        ((2 * y) ^ (9 : ℕ) / (Nat.factorial 9 : ℝ)) * 3 :=
    mul_le_mul_of_nonneg_left hexp.le hpow
  rw [thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
    thetaCuspExpTwoTaylorEightPolynomial_eval]
  norm_num at htail ⊢
  nlinarith

theorem thetaCuspThirtySecondExpTaylorLower_le_exp :
    thetaCuspThirtySecondExpTaylorLower ≤ Real.exp (1 / 32 : ℝ) := by
  rw [thetaCuspThirtySecondExpTaylorLower]
  convert thetaCuspExpTwoTaylorEightPolynomial_le_exp
    (y := (1 / 64 : ℝ)) (by norm_num) using 1
  all_goals norm_num

theorem exp_le_thetaCuspThirtySecondExpTaylorUpper :
    Real.exp (1 / 32 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
  rw [thetaCuspThirtySecondExpTaylorUpper]
  convert exp_le_thetaCuspExpTwoTaylorEightUpperPolynomial
    (y := (1 / 64 : ℝ)) (by norm_num) (by norm_num) using 1
  all_goals norm_num

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
  (ThetaRationalQuadrature.endpointLower j : ℚ)

def thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 (j : ℕ) : ℝ :=
  (ThetaRationalQuadrature.endpointUpper j : ℚ)

def thetaCuspFirstRateTaylorLocalLowerCertificate64 (j : ℕ) : ℝ[X] :=
  (expNegTruncPoly 6).comp (thetaCuspFirstRateTaylorUpperDelta64 j)

def thetaCuspFirstRateTaylorLocalUpperCertificate64 (j : ℕ) : ℝ[X] :=
  (expNegTruncPoly 5).comp (thetaCuspFirstRateTaylorLowerDelta64 j)

theorem thetaCuspFirstRateTaylorUpperEndpoint64_nonneg
    {j : ℕ} (_hj : j < 64) :
    0 ≤ thetaCuspFirstRateTaylorUpperEndpoint64 j := by
  let x : ℝ := (j : ℝ) / 64
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hexp : 2 * x ≤ Real.exp (2 * x) - 1 := by
    nlinarith [Real.add_one_le_exp (2 * x)]
  have hmul : 3 * (2 * x) ≤ Real.pi * (Real.exp (2 * x) - 1) := by
    exact mul_le_mul Real.pi_gt_three.le hexp (by nlinarith) (by positivity)
  have hrate0 : 0 ≤ thetaCuspFirstLiouvilleRate x := by
    rw [thetaCuspFirstLiouvilleRate]
    nlinarith
  have hb := (thetaCuspFirstLiouvilleRate_taylor_bounds64
    (j := j) (y := (0 : ℝ)) (by norm_num) (by norm_num)).2
  have hdelta : (thetaCuspFirstRateTaylorUpperDelta64 j).eval 0 = 0 := by
    norm_num [thetaCuspFirstRateTaylorUpperDelta64,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  dsimp only [x] at hrate0
  rw [hdelta, add_zero] at hb
  linarith

theorem thetaCuspFirstRateTaylorLowerEndpoint64_nonneg
    {j : ℕ} (_hj : j < 64) :
    0 ≤ thetaCuspFirstRateTaylorLowerEndpoint64 j := by
  have hbern := one_add_mul_le_pow
    (a := thetaCuspThirtySecondExpTaylorLower - 1) (n := j)
    (by norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial])
  have hpow : 1 + (j : ℝ) *
      (thetaCuspThirtySecondExpTaylorLower - 1) ≤
      thetaCuspThirtySecondExpTaylorLower ^ j := by
    rw [show 1 + (thetaCuspThirtySecondExpTaylorLower - 1) =
      thetaCuspThirtySecondExpTaylorLower by ring] at hbern
    exact hbern
  have hslope : (5 / 128 : ℝ) ≤
      (3.14159265358979323846 : ℝ) *
        (thetaCuspThirtySecondExpTaylorLower - 1) := by
    norm_num [thetaCuspThirtySecondExpTaylorLower,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hscaled := mul_le_mul_of_nonneg_left hslope hj0
  rw [thetaCuspFirstRateTaylorLowerEndpoint64]
  nlinarith

theorem thetaCuspFirstRateTaylorUpperEndpoint64_lt_hundredMillion
    {j : ℕ} (hj : j < 64) :
    thetaCuspFirstRateTaylorUpperEndpoint64 j < 100000000 := by
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hj64 : j ≤ 64 := by omega
  have hpow := pow_le_pow_right₀ hbase hj64
  have hcap : thetaCuspThirtySecondExpTaylorUpper ^ (64 : ℕ) < (8 : ℝ) := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow8 := hpow.trans_lt hcap
  rw [thetaCuspFirstRateTaylorUpperEndpoint64]
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

theorem thetaRationalQuadrature_thirtySecondExpLower_cast :
    (ThetaRationalQuadrature.thirtySecondExpLower : ℝ) =
      thetaCuspThirtySecondExpTaylorLower := by
  norm_num [ThetaRationalQuadrature.thirtySecondExpLower,
    ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylor,
    thetaCuspThirtySecondExpTaylorLower,
    thetaCuspExpTwoTaylorEightPolynomial]

theorem thetaRationalQuadrature_thirtySecondExpUpper_cast :
    (ThetaRationalQuadrature.thirtySecondExpUpper : ℝ) =
      thetaCuspThirtySecondExpTaylorUpper := by
  norm_num [ThetaRationalQuadrature.thirtySecondExpUpper,
    ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylorUpper,
    ThetaRationalQuadrature.add, ThetaRationalQuadrature.mul,
    ThetaRationalQuadrature.scale, ThetaRationalQuadrature.pow,
    ThetaRationalQuadrature.C, ThetaRationalQuadrature.X,
    ThetaRationalQuadrature.expTwoTaylor,
    thetaCuspThirtySecondExpTaylorUpper,
    thetaCuspExpTwoTaylorEightUpperPolynomial,
    thetaCuspExpTwoTaylorEightPolynomial]

theorem thetaRationalQuadrature_roundDown_le (x : ℚ) :
    ThetaRationalQuadrature.roundDown x ≤ x := by
  rw [ThetaRationalQuadrature.roundDown,
    div_le_iff₀ (by norm_num : (0 : ℚ) < 1000000000000)]
  exact Rat.floor_le (x * 1000000000000)

theorem thetaRationalQuadrature_le_roundUp (x : ℚ) :
    x ≤ ThetaRationalQuadrature.roundUp x := by
  rw [ThetaRationalQuadrature.roundUp,
    le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000000000)]
  exact Rat.le_ceil

theorem thetaRationalQuadrature_upperIncrement_pos (j : ℕ) :
    0 < ThetaRationalQuadrature.upperIncrement j := by
  have hbase : (1 : ℚ) ≤ ThetaRationalQuadrature.thirtySecondExpUpper := by
    norm_num [ThetaRationalQuadrature.thirtySecondExpUpper,
      ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylorUpper,
      ThetaRationalQuadrature.add, ThetaRationalQuadrature.mul,
      ThetaRationalQuadrature.scale, ThetaRationalQuadrature.pow,
      ThetaRationalQuadrature.C, ThetaRationalQuadrature.X,
      ThetaRationalQuadrature.expTwoTaylor]
  have hpow : (1 : ℚ) ≤ ThetaRationalQuadrature.thirtySecondExpUpper ^ j :=
    one_le_pow₀ hbase
  have hseed : (0 : ℚ) <
      3.14159265358979323847 *
        (ThetaRationalQuadrature.thirtySecondExpUpper - 1) - 5 / 128 := by
    norm_num [ThetaRationalQuadrature.thirtySecondExpUpper,
      ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylorUpper,
      ThetaRationalQuadrature.add, ThetaRationalQuadrature.mul,
      ThetaRationalQuadrature.scale, ThetaRationalQuadrature.pow,
      ThetaRationalQuadrature.C, ThetaRationalQuadrature.X,
      ThetaRationalQuadrature.expTwoTaylor]
  have hdiff : 0 ≤ ThetaRationalQuadrature.thirtySecondExpUpper - 1 :=
    sub_nonneg.mpr hbase
  have hmul :
      3.14159265358979323847 *
          (ThetaRationalQuadrature.thirtySecondExpUpper - 1) ≤
        3.14159265358979323847 *
          ThetaRationalQuadrature.thirtySecondExpUpper ^ j *
            (ThetaRationalQuadrature.thirtySecondExpUpper - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hpow hdiff]
  rw [ThetaRationalQuadrature.upperIncrement]
  linarith

theorem thetaRationalQuadrature_lowerIncrement_pos (j : ℕ) :
    0 < ThetaRationalQuadrature.lowerIncrement j := by
  have hbase : (1 : ℚ) ≤ ThetaRationalQuadrature.thirtySecondExpLower := by
    norm_num [ThetaRationalQuadrature.thirtySecondExpLower,
      ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylor]
  have hpow : (1 : ℚ) ≤ ThetaRationalQuadrature.thirtySecondExpLower ^ j :=
    one_le_pow₀ hbase
  have hseed : (0 : ℚ) <
      3.14159265358979323846 *
        (ThetaRationalQuadrature.thirtySecondExpLower - 1) - 5 / 128 := by
    norm_num [ThetaRationalQuadrature.thirtySecondExpLower,
      ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylor]
  have hdiff : 0 ≤ ThetaRationalQuadrature.thirtySecondExpLower - 1 :=
    sub_nonneg.mpr hbase
  have hmul :
      3.14159265358979323846 *
          (ThetaRationalQuadrature.thirtySecondExpLower - 1) ≤
        3.14159265358979323846 *
          ThetaRationalQuadrature.thirtySecondExpLower ^ j *
            (ThetaRationalQuadrature.thirtySecondExpLower - 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hpow hdiff]
  rw [ThetaRationalQuadrature.lowerIncrement]
  linarith

theorem thetaRationalQuadrature_upperIncrement_le_one
    {j : ℕ} (hj : j < 64) : ThetaRationalQuadrature.upperIncrement j ≤ 1 := by
  have hbase : (1 : ℚ) ≤ ThetaRationalQuadrature.thirtySecondExpUpper := by
    norm_num [ThetaRationalQuadrature.thirtySecondExpUpper,
      ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylorUpper,
      ThetaRationalQuadrature.add, ThetaRationalQuadrature.mul,
      ThetaRationalQuadrature.scale, ThetaRationalQuadrature.pow,
      ThetaRationalQuadrature.C, ThetaRationalQuadrature.X,
      ThetaRationalQuadrature.expTwoTaylor]
  have hpow : ThetaRationalQuadrature.thirtySecondExpUpper ^ j ≤
      ThetaRationalQuadrature.thirtySecondExpUpper ^ (64 : ℕ) :=
    pow_le_pow_right₀ hbase (by omega)
  have hdiff : 0 ≤ ThetaRationalQuadrature.thirtySecondExpUpper - 1 :=
    sub_nonneg.mpr hbase
  have hmul := mul_le_mul_of_nonneg_right hpow hdiff
  have hweighted := mul_le_mul_of_nonneg_left hmul
    (by norm_num : (0 : ℚ) ≤ 3.14159265358979323847)
  have hcap :
      3.14159265358979323847 *
          ThetaRationalQuadrature.thirtySecondExpUpper ^ (64 : ℕ) *
            (ThetaRationalQuadrature.thirtySecondExpUpper - 1) - 5 / 128 <
        (1 : ℚ) := by
    norm_num [ThetaRationalQuadrature.thirtySecondExpUpper,
      ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expTwoTaylorUpper,
      ThetaRationalQuadrature.add, ThetaRationalQuadrature.mul,
      ThetaRationalQuadrature.scale, ThetaRationalQuadrature.pow,
      ThetaRationalQuadrature.C, ThetaRationalQuadrature.X,
      ThetaRationalQuadrature.expTwoTaylor]
  rw [ThetaRationalQuadrature.upperIncrement]
  linarith

theorem thetaRationalQuadrature_expNeg_ten_cast (x : ℚ) :
    (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10) x : ℝ) =
      (expNegTruncPoly 10).eval (x : ℝ) := by
  norm_num [ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expNeg,
    eval_expNegTruncPoly, Finset.sum_range_succ]
  ring

theorem thetaRationalQuadrature_expNeg_nine_cast (x : ℚ) :
    (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 9) x : ℝ) =
      (expNegTruncPoly 9).eval (x : ℝ) := by
  norm_num [ThetaRationalQuadrature.eval, ThetaRationalQuadrature.expNeg,
    eval_expNegTruncPoly, Finset.sum_range_succ]
  ring

theorem expNegTruncPoly_ten_eval_pos_of_mem_unit
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (expNegTruncPoly 10).eval t := by
  have hid : (expNegTruncPoly 10).eval t =
      (1 - t) + t ^ (2 : ℕ) * (3 - t) / 6 + t ^ (4 : ℕ) * (5 - t) / 120 +
        t ^ (6 : ℕ) * (7 - t) / 5040 + t ^ (8 : ℕ) * (9 - t) / 362880 := by
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
    ring
  rw [hid]
  rcases ht0.eq_or_lt with rfl | htpos
  · norm_num
  · have hfirst : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsecond : 0 < t ^ (2 : ℕ) * (3 - t) / 6 := by
      exact div_pos (mul_pos (sq_pos_of_pos htpos) (by linarith)) (by norm_num)
    have hfourth : 0 ≤ t ^ (4 : ℕ) * (5 - t) / 120 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 4) (by linarith)) (by norm_num)
    have hsixth : 0 ≤ t ^ (6 : ℕ) * (7 - t) / 5040 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 6) (by linarith)) (by norm_num)
    have heighth : 0 ≤ t ^ (8 : ℕ) * (9 - t) / 362880 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 8) (by linarith)) (by norm_num)
    linarith

theorem expNegTruncPoly_ten_eval_le_exp {t : ℝ} (ht : 0 ≤ t) :
    (expNegTruncPoly 10).eval t ≤ Real.exp (-t) := by
  rcases ht.eq_or_lt with rfl | htpos
  · norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 10) (by norm_num) htpos
    norm_num at h
    exact h.le

theorem exp_le_expNegTruncPoly_nine_eval {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (expNegTruncPoly 9).eval t := by
  rcases ht.eq_or_lt with rfl | htpos
  · norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 9) (by norm_num) htpos
    norm_num at h
    exact h.le

theorem thetaCuspFirstRateTaylorUpperEndpoint64_succ (j : ℕ) :
    thetaCuspFirstRateTaylorUpperEndpoint64 (j + 1) =
      thetaCuspFirstRateTaylorUpperEndpoint64 j +
        (ThetaRationalQuadrature.upperIncrement j : ℝ) := by
  rw [thetaCuspFirstRateTaylorUpperEndpoint64,
    thetaCuspFirstRateTaylorUpperEndpoint64,
    ThetaRationalQuadrature.upperIncrement]
  push_cast
  rw [thetaRationalQuadrature_thirtySecondExpUpper_cast, pow_succ]
  ring

theorem thetaCuspFirstRateTaylorLowerEndpoint64_succ (j : ℕ) :
    thetaCuspFirstRateTaylorLowerEndpoint64 (j + 1) =
      thetaCuspFirstRateTaylorLowerEndpoint64 j +
        (ThetaRationalQuadrature.lowerIncrement j : ℝ) := by
  rw [thetaCuspFirstRateTaylorLowerEndpoint64,
    thetaCuspFirstRateTaylorLowerEndpoint64,
    ThetaRationalQuadrature.lowerIncrement]
  push_cast
  rw [thetaRationalQuadrature_thirtySecondExpLower_cast, pow_succ]
  ring

theorem thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_le_exp
    {j : ℕ} (hj : j < 64) :
    thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j ≤
      Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) := by
  induction j with
  | zero => norm_num [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64,
      ThetaRationalQuadrature.endpointLower,
      thetaCuspFirstRateTaylorUpperEndpoint64]
  | succ j ih =>
      have ih' := ih (by omega)
      have hroundQ := thetaRationalQuadrature_roundDown_le
        (ThetaRationalQuadrature.endpointLower j *
          ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
            (ThetaRationalQuadrature.upperIncrement j))
      have hround :
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 (j + 1) ≤
            thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
              (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
                (ThetaRationalQuadrature.upperIncrement j) : ℚ) := by
        rw [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64,
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64,
          ThetaRationalQuadrature.endpointLower]
        exact_mod_cast hroundQ
      have ht0q := (thetaRationalQuadrature_upperIncrement_pos j).le
      have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.upperIncrement j : ℚ) := by
        exact_mod_cast ht0q
      have ht1q := thetaRationalQuadrature_upperIncrement_le_one
        (j := j) (by omega)
      have ht1 : (ThetaRationalQuadrature.upperIncrement j : ℚ) ≤ (1 : ℝ) := by
        exact_mod_cast ht1q
      have hstep0 : (0 : ℝ) <
          (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
            (ThetaRationalQuadrature.upperIncrement j) : ℚ) := by
        rw [thetaRationalQuadrature_expNeg_ten_cast]
        exact expNegTruncPoly_ten_eval_pos_of_mem_unit ht0 ht1
      have hstep :
          (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
              (ThetaRationalQuadrature.upperIncrement j) : ℚ) ≤
            Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℚ)) := by
        rw [thetaRationalQuadrature_expNeg_ten_cast]
        exact expNegTruncPoly_ten_eval_le_exp ht0
      calc
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 (j + 1) ≤
            thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
              (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
                (ThetaRationalQuadrature.upperIncrement j) : ℚ) := hround
        _ ≤ Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) *
              Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℚ)) :=
          mul_le_mul ih' hstep hstep0.le (Real.exp_pos _).le
        _ = Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 (j + 1)) := by
          rw [thetaCuspFirstRateTaylorUpperEndpoint64_succ, neg_add, Real.exp_add]

theorem exp_le_thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64
    {j : ℕ} (_hj : j < 64) :
    Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 j) ≤
      thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j := by
  have hall (n : ℕ) :
      Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 n) ≤
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 n := by
    induction n with
    | zero => norm_num [thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64,
        ThetaRationalQuadrature.endpointUpper,
        thetaCuspFirstRateTaylorLowerEndpoint64]
    | succ n ih =>
        have hroundQ := thetaRationalQuadrature_le_roundUp
          (ThetaRationalQuadrature.endpointUpper n *
            ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 9)
              (ThetaRationalQuadrature.lowerIncrement n))
        have hround :
            thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 n *
                (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 9)
                  (ThetaRationalQuadrature.lowerIncrement n) : ℚ) ≤
              thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 (n + 1) := by
          rw [thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64,
            thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64,
            ThetaRationalQuadrature.endpointUpper]
          exact_mod_cast hroundQ
        have ht0q := (thetaRationalQuadrature_lowerIncrement_pos n).le
        have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.lowerIncrement n : ℚ) := by
          exact_mod_cast ht0q
        have hstep : Real.exp (-(ThetaRationalQuadrature.lowerIncrement n : ℚ)) ≤
            (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 9)
              (ThetaRationalQuadrature.lowerIncrement n) : ℚ) := by
          rw [thetaRationalQuadrature_expNeg_nine_cast]
          exact exp_le_expNegTruncPoly_nine_eval ht0
        have hcert0 :
            0 ≤ thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 n :=
          (Real.exp_pos _).le.trans ih
        calc
          Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 (n + 1)) =
              Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 n) *
                Real.exp (-(ThetaRationalQuadrature.lowerIncrement n : ℚ)) := by
            rw [thetaCuspFirstRateTaylorLowerEndpoint64_succ, neg_add, Real.exp_add]
          _ ≤ thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 n *
                (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 9)
                  (ThetaRationalQuadrature.lowerIncrement n) : ℚ) :=
            mul_le_mul ih hstep (Real.exp_pos _).le hcert0
          _ ≤ thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 (n + 1) := hround
  exact hall j

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
  have hbase : (1 : ℝ) ≤ thetaCuspThirtySecondExpTaylorUpper := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  have hpow : thetaCuspThirtySecondExpTaylorUpper ^ j ≤
      thetaCuspThirtySecondExpTaylorUpper ^ (64 : ℕ) :=
    pow_le_pow_right₀ hbase (by omega)
  have hlocal : thetaCuspExpTwoTaylorEightUpperPolynomial.eval y ≤
      thetaCuspExpTwoTaylorEightUpperPolynomial.eval (1 / 64) := by
    rw [thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
      thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
      thetaCuspExpTwoTaylorEightPolynomial_eval,
      thetaCuspExpTwoTaylorEightPolynomial_eval]
    norm_num at h2 h3 h4 h5 h6 h7 h8 h9 ⊢
    nlinarith
  have hdiff0 : 0 ≤ thetaCuspExpTwoTaylorEightUpperPolynomial.eval y - 1 := by
    rw [thetaCuspExpTwoTaylorEightUpperPolynomial_eval,
      thetaCuspExpTwoTaylorEightPolynomial_eval]
    nlinarith [pow_nonneg hy 2, pow_nonneg hy 3, pow_nonneg hy 4,
      pow_nonneg hy 5, pow_nonneg hy 6, pow_nonneg hy 7,
      pow_nonneg hy 8, pow_nonneg hy 9]
  have hproduct : thetaCuspThirtySecondExpTaylorUpper ^ j *
        (thetaCuspExpTwoTaylorEightUpperPolynomial.eval y - 1) ≤
      thetaCuspThirtySecondExpTaylorUpper ^ (64 : ℕ) *
        (thetaCuspExpTwoTaylorEightUpperPolynomial.eval (1 / 64) - 1) := by
    exact mul_le_mul hpow (sub_le_sub_right hlocal 1) hdiff0
      (pow_nonneg (by norm_num [thetaCuspThirtySecondExpTaylorUpper,
        thetaCuspExpTwoTaylorEightUpperPolynomial,
        thetaCuspExpTwoTaylorEightPolynomial]) _)
  have hcap : (3.14159265358979323847 : ℝ) *
      (thetaCuspThirtySecondExpTaylorUpper ^ (64 : ℕ) *
        (thetaCuspExpTwoTaylorEightUpperPolynomial.eval (1 / 64) - 1)) < 1 := by
    norm_num [thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  rw [thetaCuspFirstRateTaylorUpperDelta64]
  simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X]
  have hweighted := mul_le_mul_of_nonneg_left hproduct
    (by norm_num : (0 : ℝ) ≤ 3.14159265358979323847)
  nlinarith

theorem expNegTruncPoly_six_eval_pos_of_mem_unit
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (expNegTruncPoly 6).eval t := by
  have hid : (expNegTruncPoly 6).eval t =
      (1 - t) + t ^ (2 : ℕ) * (3 - t) / 6 + t ^ (4 : ℕ) * (5 - t) / 120 +
        0 := by
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
    ring
  rw [hid]
  rcases ht0.eq_or_lt with rfl | htpos
  · norm_num
  · have hfirst : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsecond : 0 < t ^ (2 : ℕ) * (3 - t) / 6 := by
      exact div_pos (mul_pos (sq_pos_of_pos htpos) (by linarith)) (by norm_num)
    have hfourth : 0 ≤ t ^ (4 : ℕ) * (5 - t) / 120 := by
      exact div_nonneg (mul_nonneg (pow_nonneg ht0 4) (by linarith)) (by norm_num)
    linarith

theorem thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_pos
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    0 < (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y := by
  rw [thetaCuspFirstRateTaylorLocalLowerCertificate64, eval_comp]
  exact expNegTruncPoly_six_eval_pos_of_mem_unit
    (thetaCuspFirstRateTaylorUpperDelta64_eval_nonneg j hy)
    (thetaCuspFirstRateTaylorUpperDelta64_eval_le_one hj hy hyh)

theorem thetaCuspFirstRateTaylorLocalLowerCertificate64_eval_le_exp
    {j : ℕ} (_hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (_hyh : y ≤ 1 / 64) :
    (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y ≤
      Real.exp (-(thetaCuspFirstRateTaylorUpperDelta64 j).eval y) := by
  let t := (thetaCuspFirstRateTaylorUpperDelta64 j).eval y
  have ht0 : 0 ≤ t := thetaCuspFirstRateTaylorUpperDelta64_eval_nonneg j hy
  rw [thetaCuspFirstRateTaylorLocalLowerCertificate64, eval_comp]
  change (expNegTruncPoly 6).eval t ≤ Real.exp (-t)
  rcases ht0.eq_or_lt with htzero | htpos
  · rw [← htzero]
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 6) (by norm_num) htpos
    norm_num at h
    exact h.le

theorem exp_le_thetaCuspFirstRateTaylorLocalUpperCertificate64_eval
    (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y) ≤
      (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by
  rw [thetaCuspFirstRateTaylorLocalUpperCertificate64, eval_comp]
  let t := (thetaCuspFirstRateTaylorLowerDelta64 j).eval y
  have ht0 : 0 ≤ t := thetaCuspFirstRateTaylorLowerDelta64_eval_nonneg j hy
  change Real.exp (-t) ≤ (expNegTruncPoly 5).eval t
  rcases ht0.eq_or_lt with htzero | htpos
  · rw [← htzero]
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 5) (by norm_num) htpos
    norm_num at h
    exact h.le

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
          thetaCuspThirtySecondExpTaylorLower ^ j *
            thetaCuspExpTwoTaylorEightPolynomial.eval y - 3 =
        (6.28318530717958647692 : ℝ) *
          (thetaCuspThirtySecondExpTaylorLower ^ j *
            thetaCuspExpTwoTaylorEightPolynomial.eval y) - 3 := by ring
    _ ≤
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
      thetaCuspExpTwoTaylorEightUpperPolynomial.eval y :=
    (Real.exp_pos _).le.trans hproduct
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
    _ = (6.28318530717958647694 : ℝ) *
          thetaCuspThirtySecondExpTaylorUpper ^ j *
            thetaCuspExpTwoTaylorEightUpperPolynomial.eval y - 3 := by ring

private theorem expNegTruncPoly_ten_error_le
    {t : ℝ} (ht0 : 0 ≤ t) :
    |Real.exp (-t) - (expNegTruncPoly 10).eval t| ≤
      (t ^ (10 : ℕ) / ((10 : ℕ).factorial : ℝ)) * Real.exp t := by
  have h := norm_complex_exp_sub_sum_le_factorial_tail ((-t : ℝ) : ℂ) 10
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0] at h
  rw [show (∑ m ∈ Finset.range 10,
      (((-t : ℝ) : ℂ) ^ m / (m.factorial : ℕ))) =
      (((expNegTruncPoly 10).eval t : ℝ) : ℂ) by
        push_cast
        norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
        ring] at h
  simp only [Complex.ofReal_neg] at h
  have harg : -(t : ℂ) = ((-t : ℝ) : ℂ) := by norm_num
  rw [harg, ← Complex.ofReal_exp] at h
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

private theorem exp_mul_one_sub_endpointDelta_le_expNegTruncPoly_ten
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t) *
        (1 - 9 * t ^ (10 : ℕ) / ((10 : ℕ).factorial : ℝ)) ≤
      (expNegTruncPoly 10).eval t := by
  have herr := expNegTruncPoly_ten_error_le ht0
  have hexpUpper : Real.exp t < 3 := by
    exact (Real.exp_le_exp.mpr ht1).trans_lt
      (Real.exp_one_lt_d9.trans (by norm_num))
  have hexpLower : (1 / 3 : ℝ) < Real.exp (-t) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (Real.exp_pos t) hexpUpper
  have hratio : Real.exp t ≤ 9 * Real.exp (-t) := by
    nlinarith
  have hpow : 0 ≤ t ^ (10 : ℕ) / ((10 : ℕ).factorial : ℝ) := by positivity
  have herrorUpper :
      Real.exp (-t) - (expNegTruncPoly 10).eval t ≤
        (t ^ (10 : ℕ) / ((10 : ℕ).factorial : ℝ)) * Real.exp t :=
    (le_abs_self _).trans herr
  have hscaled := mul_le_mul_of_nonneg_left hratio hpow
  nlinarith

private def thetaRationalQuadratureEndpointFactor (j : ℕ) : ℝ :=
  (ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
    (ThetaRationalQuadrature.upperIncrement j) : ℚ)

private def thetaRationalQuadratureEndpointDelta (j : ℕ) : ℝ :=
  9 * (ThetaRationalQuadrature.upperIncrement j : ℝ) ^ (10 : ℕ) /
    ((10 : ℕ).factorial : ℝ)

private theorem thetaRationalQuadratureEndpointDelta_nonneg (j : ℕ) :
    0 ≤ thetaRationalQuadratureEndpointDelta j := by
  unfold thetaRationalQuadratureEndpointDelta
  positivity

private theorem thetaRationalQuadratureEndpointDelta_le_one
    {j : ℕ} (hj : j < 64) :
    thetaRationalQuadratureEndpointDelta j ≤ 1 := by
  have ht0q := (thetaRationalQuadrature_upperIncrement_pos j).le
  have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.upperIncrement j : ℚ) := by
    exact_mod_cast ht0q
  have ht1q := thetaRationalQuadrature_upperIncrement_le_one hj
  have ht1 : (ThetaRationalQuadrature.upperIncrement j : ℚ) ≤ (1 : ℝ) := by
    exact_mod_cast ht1q
  have hp : (ThetaRationalQuadrature.upperIncrement j : ℝ) ^ (10 : ℕ) ≤ 1 := by
    simpa using pow_le_one₀ ht0 ht1
  unfold thetaRationalQuadratureEndpointDelta
  norm_num at hp ⊢
  nlinarith

private theorem thetaRationalQuadratureEndpointFactor_nonneg
    {j : ℕ} (hj : j < 64) :
    0 ≤ thetaRationalQuadratureEndpointFactor j := by
  have ht0q := (thetaRationalQuadrature_upperIncrement_pos j).le
  have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.upperIncrement j : ℚ) := by
    exact_mod_cast ht0q
  have ht1q := thetaRationalQuadrature_upperIncrement_le_one hj
  have ht1 : (ThetaRationalQuadrature.upperIncrement j : ℚ) ≤ (1 : ℝ) := by
    exact_mod_cast ht1q
  unfold thetaRationalQuadratureEndpointFactor
  rw [thetaRationalQuadrature_expNeg_ten_cast]
  exact (expNegTruncPoly_ten_eval_pos_of_mem_unit ht0 ht1).le

private theorem thetaRationalQuadratureEndpointFactor_le_one (j : ℕ) :
    thetaRationalQuadratureEndpointFactor j ≤ 1 := by
  have ht0q := (thetaRationalQuadrature_upperIncrement_pos j).le
  have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.upperIncrement j : ℚ) := by
    exact_mod_cast ht0q
  unfold thetaRationalQuadratureEndpointFactor
  rw [thetaRationalQuadrature_expNeg_ten_cast]
  exact (expNegTruncPoly_ten_eval_le_exp ht0).trans
    (Real.exp_le_one_iff.mpr (by linarith))

private theorem thetaRationalQuadratureEndpointFactor_lower
    {j : ℕ} (hj : j < 64) :
    Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℝ)) *
        (1 - thetaRationalQuadratureEndpointDelta j) ≤
      thetaRationalQuadratureEndpointFactor j := by
  have ht0q := (thetaRationalQuadrature_upperIncrement_pos j).le
  have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.upperIncrement j : ℚ) := by
    exact_mod_cast ht0q
  have ht1q := thetaRationalQuadrature_upperIncrement_le_one hj
  have ht1 : (ThetaRationalQuadrature.upperIncrement j : ℚ) ≤ (1 : ℝ) := by
    exact_mod_cast ht1q
  unfold thetaRationalQuadratureEndpointFactor thetaRationalQuadratureEndpointDelta
  rw [thetaRationalQuadrature_expNeg_ten_cast]
  exact exp_mul_one_sub_endpointDelta_le_expNegTruncPoly_ten ht0 ht1

private theorem sum_upperIncrement_eq_endpoint (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (ThetaRationalQuadrature.upperIncrement j : ℝ)) =
        thetaCuspFirstRateTaylorUpperEndpoint64 n := by
  induction n with
  | zero => norm_num [thetaCuspFirstRateTaylorUpperEndpoint64]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih,
        thetaCuspFirstRateTaylorUpperEndpoint64_succ]

private theorem thetaCuspFirstRateTaylorUpperEndpoint64_le_eighteen
    {n : ℕ} (hn : n ≤ 64) :
    thetaCuspFirstRateTaylorUpperEndpoint64 n ≤ 18 := by
  have hmono : Monotone thetaCuspFirstRateTaylorUpperEndpoint64 :=
    monotone_nat_of_le_succ fun j => by
      rw [thetaCuspFirstRateTaylorUpperEndpoint64_succ]
      exact le_add_of_nonneg_right (by
        exact_mod_cast (thetaRationalQuadrature_upperIncrement_pos j).le)
  have hcap : thetaCuspFirstRateTaylorUpperEndpoint64 64 < 18 := by
    norm_num [thetaCuspFirstRateTaylorUpperEndpoint64,
      thetaCuspThirtySecondExpTaylorUpper,
      thetaCuspExpTwoTaylorEightUpperPolynomial,
      thetaCuspExpTwoTaylorEightPolynomial]
  exact (hmono hn).trans hcap.le

private theorem thetaRationalQuadratureEndpointDelta_le_nine_div_factorial
    {j : ℕ} (hj : j < 64) :
    thetaRationalQuadratureEndpointDelta j ≤
      9 / ((10 : ℕ).factorial : ℝ) := by
  have ht0q := (thetaRationalQuadrature_upperIncrement_pos j).le
  have ht0 : (0 : ℝ) ≤ (ThetaRationalQuadrature.upperIncrement j : ℚ) := by
    exact_mod_cast ht0q
  have ht1q := thetaRationalQuadrature_upperIncrement_le_one hj
  have ht1 : (ThetaRationalQuadrature.upperIncrement j : ℚ) ≤ (1 : ℝ) := by
    exact_mod_cast ht1q
  have hp : (ThetaRationalQuadrature.upperIncrement j : ℝ) ^ (10 : ℕ) ≤ 1 := by
    simpa using pow_le_one₀ ht0 ht1
  unfold thetaRationalQuadratureEndpointDelta
  norm_num at ⊢
  nlinarith

private theorem sum_endpointDelta_lt_one_thousandth
    {n : ℕ} (hn : n ≤ 64) :
    (∑ j ∈ Finset.range n, thetaRationalQuadratureEndpointDelta j) <
      (1 / 1000 : ℝ) := by
  calc
    (∑ j ∈ Finset.range n, thetaRationalQuadratureEndpointDelta j) ≤
        ∑ _j ∈ Finset.range n,
          (9 / ((10 : ℕ).factorial : ℝ)) := by
      exact Finset.sum_le_sum fun j hj =>
        thetaRationalQuadratureEndpointDelta_le_nine_div_factorial
          (Finset.mem_range.mp hj |>.trans_le hn)
    _ = (n : ℝ) * (9 / ((10 : ℕ).factorial : ℝ)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (64 : ℝ) * (9 / ((10 : ℕ).factorial : ℝ)) := by
      gcongr
      exact_mod_cast hn
    _ < (1 / 1000 : ℝ) := by norm_num

private theorem endpointFactor_prod_lower
    {n : ℕ} (hn : n ≤ 64) :
    Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 n) *
        (1 - ∑ j ∈ Finset.range n,
          thetaRationalQuadratureEndpointDelta j) ≤
      ∏ j ∈ Finset.range n, thetaRationalQuadratureEndpointFactor j := by
  have hprodLower :
      (∏ j ∈ Finset.range n,
          Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℝ)) *
            (1 - thetaRationalQuadratureEndpointDelta j)) ≤
        ∏ j ∈ Finset.range n, thetaRationalQuadratureEndpointFactor j := by
    apply Finset.prod_le_prod
    · intro j hj
      exact mul_nonneg (Real.exp_pos _).le
        (sub_nonneg.mpr (thetaRationalQuadratureEndpointDelta_le_one
          (Finset.mem_range.mp hj |>.trans_le hn)))
    · intro j hj
      exact thetaRationalQuadratureEndpointFactor_lower
        (Finset.mem_range.mp hj |>.trans_le hn)
  have hbonf := one_sub_sum_le_prod_one_sub (Finset.range n)
    thetaRationalQuadratureEndpointDelta
    (fun j _hj => thetaRationalQuadratureEndpointDelta_nonneg j)
    (fun j hj => thetaRationalQuadratureEndpointDelta_le_one
      (Finset.mem_range.mp hj |>.trans_le hn))
  have hexpProdNonneg :
      0 ≤ ∏ j ∈ Finset.range n,
        Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℝ)) :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hweighted := mul_le_mul_of_nonneg_left hbonf hexpProdNonneg
  calc
    Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 n) *
          (1 - ∑ j ∈ Finset.range n,
            thetaRationalQuadratureEndpointDelta j) =
        (∏ j ∈ Finset.range n,
          Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℝ))) *
            (1 - ∑ j ∈ Finset.range n,
              thetaRationalQuadratureEndpointDelta j) := by
      rw [← Real.exp_sum]
      congr 2
      rw [Finset.sum_neg_distrib, sum_upperIncrement_eq_endpoint]
    _ ≤ (∏ j ∈ Finset.range n,
          Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℝ))) *
            (∏ j ∈ Finset.range n,
              (1 - thetaRationalQuadratureEndpointDelta j)) := hweighted
    _ = ∏ j ∈ Finset.range n,
          (Real.exp (-(ThetaRationalQuadrature.upperIncrement j : ℝ)) *
            (1 - thetaRationalQuadratureEndpointDelta j)) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ ∏ j ∈ Finset.range n,
        thetaRationalQuadratureEndpointFactor j := hprodLower

private theorem one_div_sixtySixMillion_lt_exp_neg_eighteen :
    (1 / 66000000 : ℝ) < Real.exp (-18) := by
  have hpow := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le
    (n := 18) (by norm_num)
  have hcap : Real.exp 18 < (66000000 : ℝ) := by
    rw [show (18 : ℝ) = (18 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact hpow.trans (by norm_num)
  rw [Real.exp_neg]
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (Real.exp_pos 18) hcap

private theorem fixed_lower_lt_endpointFactor_prod
    {n : ℕ} (hn : n ≤ 64) :
    (999 / 66000000000 : ℝ) <
      ∏ j ∈ Finset.range n, thetaRationalQuadratureEndpointFactor j := by
  have hprod := endpointFactor_prod_lower hn
  have hrate := thetaCuspFirstRateTaylorUpperEndpoint64_le_eighteen hn
  have hexp : Real.exp (-18) ≤
      Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 n) :=
    Real.exp_le_exp.mpr (by linarith)
  have hdelta := sum_endpointDelta_lt_one_thousandth hn
  have hone : (999 / 1000 : ℝ) <
      1 - ∑ j ∈ Finset.range n,
        thetaRationalQuadratureEndpointDelta j := by
    linarith
  have hfixed := one_div_sixtySixMillion_lt_exp_neg_eighteen
  calc
    (999 / 66000000000 : ℝ) =
        (1 / 66000000 : ℝ) * (999 / 1000) := by norm_num
    _ < Real.exp (-18) * (999 / 1000) := by gcongr
    _ ≤ Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 n) *
          (999 / 1000) := by gcongr
    _ < Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 n) *
          (1 - ∑ j ∈ Finset.range n,
            thetaRationalQuadratureEndpointDelta j) := by gcongr
    _ ≤ ∏ j ∈ Finset.range n,
        thetaRationalQuadratureEndpointFactor j := hprod

private theorem thetaRationalQuadrature_roundDown_sub_error_lt (x : ℚ) :
    x - 1 / 1000000000000 < ThetaRationalQuadrature.roundDown x := by
  rw [ThetaRationalQuadrature.roundDown,
    lt_div_iff₀ (by norm_num : (0 : ℚ) < 1000000000000)]
  calc
    (x - 1 / 1000000000000) * 1000000000000 =
        x * 1000000000000 - 1 := by ring
    _ < ((⌊x * 1000000000000⌋ : ℤ) : ℚ) :=
      Int.sub_one_lt_floor (x * 1000000000000)

private theorem endpointFactor_prod_sub_rounding_le_endpointLower
    {n : ℕ} (hn : n ≤ 64) :
    (∏ j ∈ Finset.range n, thetaRationalQuadratureEndpointFactor j) -
        (n : ℝ) / 1000000000000 ≤
      (ThetaRationalQuadrature.endpointLower n : ℚ) := by
  induction n with
  | zero => norm_num [ThetaRationalQuadrature.endpointLower]
  | succ n ih =>
      let p : ℝ := thetaRationalQuadratureEndpointFactor n
      let P : ℝ := ∏ j ∈ Finset.range n,
        thetaRationalQuadratureEndpointFactor j
      have ih' := ih (by omega)
      have hp0 : 0 ≤ p :=
        thetaRationalQuadratureEndpointFactor_nonneg (j := n) (by omega)
      have hp1 : p ≤ 1 := thetaRationalQuadratureEndpointFactor_le_one n
      have hmul : (P - (n : ℝ) / 1000000000000) * p ≤
          (ThetaRationalQuadrature.endpointLower n : ℚ) * p :=
        mul_le_mul_of_nonneg_right ih' hp0
      have hroundQ := thetaRationalQuadrature_roundDown_sub_error_lt
        (ThetaRationalQuadrature.endpointLower n *
          ThetaRationalQuadrature.eval (ThetaRationalQuadrature.expNeg 10)
            (ThetaRationalQuadrature.upperIncrement n))
      have hroundCast := (Rat.cast_lt (K := ℝ)).2 hroundQ
      have hround :
          (ThetaRationalQuadrature.endpointLower n : ℚ) * p -
              1 / 1000000000000 <
            (ThetaRationalQuadrature.endpointLower (n + 1) : ℚ) := by
        push_cast at hroundCast
        simpa only [p, thetaRationalQuadratureEndpointFactor,
          ThetaRationalQuadrature.endpointLower] using hroundCast
      have herror :
          P * p - ((n + 1 : ℕ) : ℝ) / 1000000000000 ≤
            (P - (n : ℝ) / 1000000000000) * p -
              1 / 1000000000000 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hnp : 0 ≤ (n : ℝ) * (1 - p) :=
          mul_nonneg hn0 (sub_nonneg.mpr hp1)
        apply sub_nonneg.mp
        calc
          0 ≤ (n : ℝ) * (1 - p) / 1000000000000 := by positivity
          _ = (P - (n : ℝ) / 1000000000000) * p -
                1 / 1000000000000 -
              (P * p - ((n + 1 : ℕ) : ℝ) / 1000000000000) := by
            push_cast
            ring
      rw [Finset.prod_range_succ]
      dsimp only [P, p] at hmul hround herror ⊢
      exact herror.trans (sub_le_sub_right hmul _ |>.trans hround.le)

private theorem thetaRationalQuadrature_endpointLower_pos
    {n : ℕ} (hn : n ≤ 64) :
    0 < (ThetaRationalQuadrature.endpointLower n : ℚ) := by
  have hprod := fixed_lower_lt_endpointFactor_prod hn
  have hendpoint := endpointFactor_prod_sub_rounding_le_endpointLower hn
  have hnR : (n : ℝ) ≤ 64 := by exact_mod_cast hn
  have hpositive :
      (0 : ℝ) < (999 / 66000000000 : ℝ) - 64 / 1000000000000 := by
    norm_num
  have hfixed :
      (999 / 66000000000 : ℝ) - 64 / 1000000000000 <
        (∏ j ∈ Finset.range n, thetaRationalQuadratureEndpointFactor j) -
          (n : ℝ) / 1000000000000 := by
    nlinarith
  exact_mod_cast hpositive.trans_le (hfixed.le.trans hendpoint)

theorem thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64_pos
    {j : ℕ} (hj : j < 64) :
    0 < thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j := by
  rw [thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64]
  exact_mod_cast thetaRationalQuadrature_endpointLower_pos hj.le

theorem thetaCuspFirstGibbsTaylorLower64_le
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    (0.0432139182637 : ℝ) *
        thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
        (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y ≤
      thetaCuspLiouvilleGibbsAtom 1 ((j : ℝ) / 64 + y) := by
  have hrate :=
    (thetaCuspFirstLiouvilleRate_taylor_bounds64 (j := j) hy hyh).2
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
          thetaCuspFirstRateTaylorUpperEndpointLowerCertificate64 j *
            (thetaCuspFirstRateTaylorLocalLowerCertificate64 j).eval y := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_lower hendpoint0)
        hlocal0
    _ ≤ Real.exp (-Real.pi) *
          Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) *
            Real.exp (-(thetaCuspFirstRateTaylorUpperDelta64 j).eval y) := by
      gcongr
    _ = Real.exp (-Real.pi) *
          (Real.exp (-thetaCuspFirstRateTaylorUpperEndpoint64 j) *
            Real.exp (-(thetaCuspFirstRateTaylorUpperDelta64 j).eval y)) := by ring
    _ = Real.exp (-Real.pi) *
          Real.exp (-(thetaCuspFirstRateTaylorUpperEndpoint64 j +
            (thetaCuspFirstRateTaylorUpperDelta64 j).eval y)) := by
      rw [show -(thetaCuspFirstRateTaylorUpperEndpoint64 j +
          (thetaCuspFirstRateTaylorUpperDelta64 j).eval y) =
        -thetaCuspFirstRateTaylorUpperEndpoint64 j +
          -(thetaCuspFirstRateTaylorUpperDelta64 j).eval y by ring,
        Real.exp_add]
    _ ≤ Real.exp (-Real.pi) *
          Real.exp (-thetaCuspFirstLiouvilleRate ((j : ℝ) / 64 + y)) := by
      gcongr

theorem thetaCuspFirstGibbs_le_taylorUpper64
    {j : ℕ} (hj : j < 64) {y : ℝ} (hy : 0 ≤ y) (hyh : y ≤ 1 / 64) :
    thetaCuspLiouvilleGibbsAtom 1 ((j : ℝ) / 64 + y) ≤
      (0.0432139182638 : ℝ) *
        thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
        (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by
  have hrate :=
    (thetaCuspFirstLiouvilleRate_taylor_bounds64 (j := j) hy hyh).1
  have hendpoint :=
    exp_le_thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 hj
  have hlocal := exp_le_thetaCuspFirstRateTaylorLocalUpperCertificate64_eval j hy
  have hendpointCert0 :
      0 ≤ thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j :=
    (Real.exp_pos _).le.trans hendpoint
  have hlocalCert0 :
      0 ≤ (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y :=
    (Real.exp_pos _).le.trans hlocal
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
      rw [show -(thetaCuspFirstRateTaylorLowerEndpoint64 j +
          (thetaCuspFirstRateTaylorLowerDelta64 j).eval y) =
        -thetaCuspFirstRateTaylorLowerEndpoint64 j +
          -(thetaCuspFirstRateTaylorLowerDelta64 j).eval y by ring,
        Real.exp_add]
    _ ≤ (0.0432139182638 : ℝ) *
          (Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 j) *
            Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y)) := by
      exact mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_upper
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ ≤ (0.0432139182638 : ℝ) *
          thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
          (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by
      calc
        (0.0432139182638 : ℝ) *
              (Real.exp (-thetaCuspFirstRateTaylorLowerEndpoint64 j) *
                Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y)) ≤
            (0.0432139182638 : ℝ) *
              (thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
                Real.exp (-(thetaCuspFirstRateTaylorLowerDelta64 j).eval y)) := by
          gcongr
        _ ≤ (0.0432139182638 : ℝ) *
              (thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
                (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y) := by
          gcongr
        _ = (0.0432139182638 : ℝ) *
              thetaCuspFirstRateTaylorLowerEndpointUpperCertificate64 j *
              (thetaCuspFirstRateTaylorLocalUpperCertificate64 j).eval y := by ring

end

end RHTower
