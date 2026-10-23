import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard
import GaloisForLFunctions.RHTower.VonMangoldtGammaOrientedAnomaly
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A rational analytic floor for the dominant theta atom's fourth moment

The order-fourteen squared-Xi edge corner only needs a coarse lower bound on the fourth
theta-cusp moment.  This file supplies it without zero tables or numerical integration.

On each of the seven intervals `[j/8,(j+1)/8]`, convexity of the exponential bounds
`exp (2*x)` by the chord through the adjacent quarter-exponential values.  The elementary
majorant `exp (1/4) < 257/200` makes that chord rational.  A sixty-fourth-order alternating
Taylor section controls the endpoint decay, while a positive fifth-order Taylor section
propagates the endpoint bound back across the interval.  The resulting degree-twelve
polynomials integrate exactly over rational endpoints.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- Rational majorant for one quarter of the real exponential clock. -/
def thetaCuspQuarterExpMajorant : ℝ := 257 / 200

/-- The convex rational chord used on the `j`-th interval of length `1/8`. -/
def thetaCuspQuarterExpChord (j : ℕ) (x : ℝ) : ℝ :=
  let t : ℝ := 8 * x - j
  (1 - t) * thetaCuspQuarterExpMajorant ^ j +
    t * thetaCuspQuarterExpMajorant ^ (j + 1)

/-- Exact source decay rate after extracting the boundary factor `exp (-pi)`. -/
def thetaCuspFirstLiouvilleRate (x : ℝ) : ℝ :=
  Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2

/-- Rational affine upper rate on the `j`-th interval. -/
def thetaCuspFirstLiouvilleRateMajorant (j : ℕ) (x : ℝ) : ℝ :=
  (3927 / 1250 : ℝ) * (thetaCuspQuarterExpChord j x - 1) - 5 * x / 2

/-- Slope of the affine rate majorant. -/
def thetaCuspFirstLiouvilleRateSlope (j : ℕ) : ℝ :=
  (3927 / 1250 : ℝ) * 8 *
      (thetaCuspQuarterExpMajorant ^ (j + 1) -
        thetaCuspQuarterExpMajorant ^ j) -
    5 / 2

/-- Positive Taylor section through degree five. -/
def thetaCuspExpTaylorFive (u : ℝ) : ℝ :=
  1 + u + u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 6 + u ^ (4 : ℕ) / 24 + u ^ (5 : ℕ) / 120

/-- Positive Taylor section through degree three, used for endpoint propagation. -/
def thetaCuspExpTaylorThree (u : ℝ) : ℝ :=
  1 + u + u ^ (2 : ℕ) / 2 + u ^ (3 : ℕ) / 6

/-- Alternating endpoint certificate for the `j`-th rational rate. -/
def thetaCuspFirstLiouvilleEndpointCertificate (j : ℕ) : ℝ :=
  (expNegTruncPoly 64).eval
    (thetaCuspFirstLiouvilleRateMajorant j (((j + 1 : ℕ) : ℝ) / 8))

/-- The rational lower density integrated on the `j`-th interval. -/
def thetaCuspFirstAtomFourthIntervalCertificate (j : ℕ) (x : ℝ) : ℝ :=
  (6283 / 500 : ℝ) * (3 / 70) * thetaCuspFirstLiouvilleEndpointCertificate j *
    x ^ (4 : ℕ) *
    ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
    thetaCuspExpTaylorFive
      (thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8 - x))

/-- Polynomial form of the positive Taylor section. -/
def thetaCuspExpTaylorFivePolynomial : ℝ[X] :=
  1 + X + C (1 / 2) * X ^ (2 : ℕ) + C (1 / 6) * X ^ (3 : ℕ) +
    C (1 / 24) * X ^ (4 : ℕ) + C (1 / 120) * X ^ (5 : ℕ)

/-- Polynomial form of the cubic positive Taylor section. -/
def thetaCuspExpTaylorThreePolynomial : ℝ[X] :=
  1 + X + C (1 / 2) * X ^ (2 : ℕ) + C (1 / 6) * X ^ (3 : ℕ)

theorem thetaCuspExpTaylorFivePolynomial_eval (x : ℝ) :
    thetaCuspExpTaylorFivePolynomial.eval x = thetaCuspExpTaylorFive x := by
  simp only [thetaCuspExpTaylorFivePolynomial, thetaCuspExpTaylorFive,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one]
  ring

theorem thetaCuspExpTaylorThreePolynomial_eval (x : ℝ) :
    thetaCuspExpTaylorThreePolynomial.eval x = thetaCuspExpTaylorThree x := by
  simp only [thetaCuspExpTaylorThreePolynomial, thetaCuspExpTaylorThree,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_one]
  ring

/-- Polynomial shape of one interval certificate, with its endpoint factor removed. -/
def thetaCuspFirstAtomFourthIntervalShapePolynomial (j : ℕ) : ℝ[X] :=
  C ((6283 / 500 : ℝ) * (3 / 70)) *
    X ^ (4 : ℕ) *
    (C (6283 / 1000 : ℝ) *
        thetaCuspExpTaylorFivePolynomial.comp (C 2 * X) - C 3) *
    thetaCuspExpTaylorFivePolynomial.comp
      (C (thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8)) -
        C (thetaCuspFirstLiouvilleRateSlope j) * X)

/-- Polynomial form of one interval certificate. -/
def thetaCuspFirstAtomFourthIntervalCertificatePolynomial (j : ℕ) : ℝ[X] :=
  C (thetaCuspFirstLiouvilleEndpointCertificate j) *
    thetaCuspFirstAtomFourthIntervalShapePolynomial j

theorem exp_one_quarter_lt_thetaCuspQuarterExpMajorant :
    Real.exp (1 / 4 : ℝ) < thetaCuspQuarterExpMajorant := by
  rw [thetaCuspQuarterExpMajorant]
  by_contra h
  have hle : (257 / 200 : ℝ) ≤ Real.exp (1 / 4 : ℝ) := le_of_not_gt h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 257 / 200) hle 4
  have heq : Real.exp (1 / 4 : ℝ) ^ (4 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq] at hp
  have hu : Real.exp 1 < (257 / 200 : ℝ) ^ (4 : ℕ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  linarith

theorem exp_nat_quarter_le_thetaCuspQuarterExpMajorant_pow (j : ℕ) :
    Real.exp ((j : ℝ) / 4) ≤ thetaCuspQuarterExpMajorant ^ j := by
  rw [show (j : ℝ) / 4 = (j : ℕ) * (1 / 4 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le
    exp_one_quarter_lt_thetaCuspQuarterExpMajorant.le j

/-- Convexity of the exponential supplies the rational quarter-chord majorant. -/
theorem exp_two_mul_le_thetaCuspQuarterExpChord
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 8 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 8)) :
    Real.exp (2 * x) ≤ thetaCuspQuarterExpChord j x := by
  let t : ℝ := 8 * x - j
  have ht0 : 0 ≤ t := by dsimp only [t]; push_cast at hx ⊢; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; push_cast at hx ⊢; linarith
  have hconv := convexOn_exp.2
    (Set.mem_univ ((j : ℝ) / 4))
    (Set.mem_univ (((j + 1 : ℕ) : ℝ) / 4))
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  have harg :
      (1 - t) * ((j : ℝ) / 4) +
          t * (((j + 1 : ℕ) : ℝ) / 4) = 2 * x := by
    dsimp only [t]
    push_cast
    ring
  simp only [smul_eq_mul] at hconv
  rw [harg] at hconv
  have hj := exp_nat_quarter_le_thetaCuspQuarterExpMajorant_pow j
  have hj1 := exp_nat_quarter_le_thetaCuspQuarterExpMajorant_pow (j + 1)
  calc
    Real.exp (2 * x) ≤
        (1 - t) * Real.exp ((j : ℝ) / 4) +
          t * Real.exp (((j + 1 : ℕ) : ℝ) / 4) := hconv
    _ ≤ (1 - t) * thetaCuspQuarterExpMajorant ^ j +
          t * thetaCuspQuarterExpMajorant ^ (j + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hj1 ht0)
    _ = thetaCuspQuarterExpChord j x := by
      simp only [thetaCuspQuarterExpChord, t]

/-- The exact Liouville rate lies below the rational chord rate on every certificate interval. -/
theorem thetaCuspFirstLiouvilleRate_le_majorant
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 8 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 8)) :
    thetaCuspFirstLiouvilleRate x ≤
      thetaCuspFirstLiouvilleRateMajorant j x := by
  have hx0 : 0 ≤ x := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 8 := by positivity
    linarith [hx.1]
  have hchord := exp_two_mul_le_thetaCuspQuarterExpChord hx
  have hone : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
  have hchord0 : 0 ≤ thetaCuspQuarterExpChord j x - 1 := by linarith
  have hpi : Real.pi < (3927 / 1250 : ℝ) := by
    linarith only [Real.pi_lt_d4]
  rw [thetaCuspFirstLiouvilleRate, thetaCuspFirstLiouvilleRateMajorant]
  calc
    Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2 ≤
        Real.pi * (thetaCuspQuarterExpChord j x - 1) - 5 * x / 2 := by
      gcongr
    _ ≤ (3927 / 1250 : ℝ) * (thetaCuspQuarterExpChord j x - 1) -
          5 * x / 2 := by
      gcongr

theorem thetaCuspFirstLiouvilleRateMajorant_affine
    (j : ℕ) (x : ℝ) :
    thetaCuspFirstLiouvilleRateMajorant j x =
      thetaCuspFirstLiouvilleRateMajorant j (((j + 1 : ℕ) : ℝ) / 8) -
        thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8 - x) := by
  simp only [thetaCuspFirstLiouvilleRateMajorant,
    thetaCuspFirstLiouvilleRateSlope, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant]
  push_cast
  ring

theorem thetaCuspExpTaylorFive_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaCuspExpTaylorFive u := by
  rw [thetaCuspExpTaylorFive]
  positivity

theorem thetaCuspExpTaylorFive_le_exp {u : ℝ} (hu : 0 ≤ u) :
    thetaCuspExpTaylorFive u ≤ Real.exp u := by
  have h := Real.sum_le_exp_of_nonneg hu 6
  norm_num [Finset.sum_range_succ] at h
  simpa only [thetaCuspExpTaylorFive] using h

theorem thetaCuspExpTaylorThree_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaCuspExpTaylorThree u := by
  rw [thetaCuspExpTaylorThree]
  positivity

theorem thetaCuspExpTaylorThree_le_exp {u : ℝ} (hu : 0 ≤ u) :
    thetaCuspExpTaylorThree u ≤ Real.exp u := by
  have h := Real.sum_le_exp_of_nonneg hu 4
  norm_num [Finset.sum_range_succ] at h
  simpa only [thetaCuspExpTaylorThree] using h

/-- A sharp exact boundary floor used to remove the only transcendental prefactor. -/
theorem three_div_seventy_lt_exp_neg_pi :
    (3 / 70 : ℝ) < Real.exp (-Real.pi) := by
  have he1 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have he114 : Real.exp (1 / 14 : ℝ) ≤ 14 / 13 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (x := (1 / 14 : ℝ)) (by norm_num) (by norm_num)
    convert h using 1 ; norm_num
  have he17 : Real.exp (1 / 7 : ℝ) ≤ (14 / 13 : ℝ) ^ (2 : ℕ) := by
    rw [show (1 / 7 : ℝ) = (2 : ℕ) * (1 / 14 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le he114 2
  have he3 : Real.exp 3 < (2.7182818286 : ℝ) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact pow_lt_pow_left₀ he1 (by positivity) (by norm_num)
  have hepi : Real.exp Real.pi < 70 / 3 := by
    calc
      Real.exp Real.pi < Real.exp (22 / 7 : ℝ) :=
        Real.exp_lt_exp.mpr (by linarith only [Real.pi_lt_d4])
      _ = Real.exp 3 * Real.exp (1 / 7 : ℝ) := by
        rw [show (22 / 7 : ℝ) = 3 + 1 / 7 by norm_num, Real.exp_add]
      _ < (2.7182818286 : ℝ) ^ (3 : ℕ) * Real.exp (1 / 7 : ℝ) :=
        mul_lt_mul_of_pos_right he3 (Real.exp_pos _)
      _ ≤ (2.7182818286 : ℝ) ^ (3 : ℕ) * (14 / 13 : ℝ) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left he17 (by positivity)
      _ < 70 / 3 := by norm_num
  rw [Real.exp_neg]
  have hinv :=
    (div_lt_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 70 / 3) (Real.exp_pos _)).2 hepi
  norm_num at hinv ⊢
  exact hinv

/-- Compatibility form of the earlier boundary floor. -/
theorem one_div_twentyFour_lt_exp_neg_pi :
    (1 / 24 : ℝ) < Real.exp (-Real.pi) := by
  linarith only [three_div_seventy_lt_exp_neg_pi]

theorem thetaCuspFirstLiouvilleRateSlope_pos
    {j : ℕ} (hj : j < 7) :
    0 < thetaCuspFirstLiouvilleRateSlope j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstLiouvilleRateSlope,
      thetaCuspQuarterExpMajorant]

theorem thetaCuspFirstLiouvilleRateMajorant_endpoint_pos
    {j : ℕ} (hj : j < 7) :
    0 < thetaCuspFirstLiouvilleRateMajorant j (((j + 1 : ℕ) : ℝ) / 8) := by
  interval_cases j <;>
    norm_num [thetaCuspFirstLiouvilleRateMajorant,
      thetaCuspQuarterExpChord, thetaCuspQuarterExpMajorant]

theorem thetaCuspFirstLiouvilleEndpointCertificate_pos
    {j : ℕ} (hj : j < 7) :
    0 < thetaCuspFirstLiouvilleEndpointCertificate j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstLiouvilleEndpointCertificate,
      thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
      thetaCuspQuarterExpMajorant, eval_expNegTruncPoly,
      Finset.sum_range_succ]

theorem thetaCuspFirstLiouvilleEndpointCertificate_lt_exp
    {j : ℕ} (hj : j < 7) :
    thetaCuspFirstLiouvilleEndpointCertificate j <
      Real.exp
        (-thetaCuspFirstLiouvilleRateMajorant j (((j + 1 : ℕ) : ℝ) / 8)) := by
  have hz := thetaCuspFirstLiouvilleRateMajorant_endpoint_pos hj
  have h := expNegTruncPoly_sub_exp_oriented_pos
    (m := 64) (by norm_num) hz
  norm_num at h
  rw [thetaCuspFirstLiouvilleEndpointCertificate]
  convert h using 1 <;> push_cast <;> ring

theorem thetaCuspLiouvilleGibbsAtom_one_eq_rate (x : ℝ) :
    thetaCuspLiouvilleGibbsAtom 1 x =
      Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x) := by
  rw [thetaCuspLiouvilleGibbsAtom_apply]
  simp only [Nat.cast_one, one_mul]
  rw [← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [thetaCuspFirstLiouvilleRate]
  ring

/-- The rational endpoint/Taylor certificate lies below the exact positive Gibbs atom. -/
theorem thetaCuspFirstLiouvilleIntervalCertificate_le_gibbs
    {j : ℕ} (hj : j < 7) {x : ℝ}
    (hx : (j : ℝ) / 8 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 8)) :
    (3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificate j *
        thetaCuspExpTaylorFive
          (thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8 - x)) ≤
      thetaCuspLiouvilleGibbsAtom 1 x := by
  let b : ℝ := ((j + 1 : ℕ) : ℝ) / 8
  let z : ℝ := thetaCuspFirstLiouvilleRateMajorant j b
  let k : ℝ := thetaCuspFirstLiouvilleRateSlope j
  let u : ℝ := k * (b - x)
  have hk : 0 < k := by simpa only [k] using thetaCuspFirstLiouvilleRateSlope_pos hj
  have hxb : 0 ≤ b - x := by dsimp only [b]; push_cast at hx ⊢; linarith
  have hu : 0 ≤ u := mul_nonneg hk.le hxb
  have hrate := thetaCuspFirstLiouvilleRate_le_majorant hx
  have haffine := thetaCuspFirstLiouvilleRateMajorant_affine j x
  have hrate' : thetaCuspFirstLiouvilleRate x ≤ z - u := by
    dsimp only [z, u, k, b]
    rw [← haffine]
    exact hrate
  have hexpRate : Real.exp (-z) * Real.exp u ≤
      Real.exp (-thetaCuspFirstLiouvilleRate x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hP := thetaCuspFirstLiouvilleEndpointCertificate_lt_exp hj
  have hP0 := thetaCuspFirstLiouvilleEndpointCertificate_pos hj
  have hT := thetaCuspExpTaylorFive_le_exp hu
  have hT0 := thetaCuspExpTaylorFive_nonneg hu
  have hPT : thetaCuspFirstLiouvilleEndpointCertificate j *
      thetaCuspExpTaylorFive u ≤ Real.exp (-z) * Real.exp u := by
    exact mul_le_mul hP.le hT hT0 (Real.exp_pos _).le
  rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    (3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificate j *
          thetaCuspExpTaylorFive
            (thetaCuspFirstLiouvilleRateSlope j *
              (((j + 1 : ℕ) : ℝ) / 8 - x)) =
        (3 / 70 : ℝ) *
          (thetaCuspFirstLiouvilleEndpointCertificate j *
            thetaCuspExpTaylorFive u) := by
      dsimp only [u, k, b]
      ring
    _ ≤ Real.exp (-Real.pi) *
          (thetaCuspFirstLiouvilleEndpointCertificate j *
            thetaCuspExpTaylorFive u) := by
      exact mul_le_mul_of_nonneg_right three_div_seventy_lt_exp_neg_pi.le
        (mul_nonneg hP0.le hT0)
    _ ≤ Real.exp (-Real.pi) * (Real.exp (-z) * Real.exp u) := by
      exact mul_le_mul_of_nonneg_left hPT (Real.exp_pos _).le
    _ ≤ Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x) := by
      exact mul_le_mul_of_nonneg_left hexpRate (Real.exp_pos _).le

theorem thetaCuspSourceTerm_one_eq_liouvilleGibbs (x : ℝ) :
    thetaCuspSourceTerm x 1 =
      2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
        thetaCuspLiouvilleGibbsAtom 1 x := by
  rw [thetaCuspSourceTerm, thetaCuspSeed,
    thetaCuspLiouvilleGibbsAtom_apply]
  simp only [Nat.cast_one, one_mul]
  rw [← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have he2 : Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
  have he4 : Real.exp (4 * x) = Real.exp x ^ (2 : ℕ) * Real.exp (2 * x) := by
    rw [he2, ← Real.exp_add]
    congr 1
    ring
  rw [he4]
  ring

theorem thetaCuspFirstAtomFourthIntervalCertificate_le_density
    {j : ℕ} (hj : j < 7) {x : ℝ}
    (hx : (j : ℝ) / 8 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 8)) :
    thetaCuspFirstAtomFourthIntervalCertificate j x ≤
      2 * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1) := by
  have hx0 : 0 ≤ x := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [hx.1]
  have hTsource := thetaCuspExpTaylorFive_le_exp
    (u := 2 * x) (by positivity)
  have hTsource0 := thetaCuspExpTaylorFive_nonneg
    (u := 2 * x) (by positivity)
  have hinner :
      (6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3 ≤
        2 * Real.pi * Real.exp (2 * x) - 3 := by
    have hpi : (6283 / 1000 : ℝ) < 2 * Real.pi := by
      linarith only [Real.pi_gt_d4]
    calc
      (6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3 ≤
          (6283 / 1000 : ℝ) * Real.exp (2 * x) - 3 := by
        gcongr
      _ ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
        gcongr
  have hinner0 :
      0 ≤ (6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3 := by
    rw [thetaCuspExpTaylorFive]
    nlinarith only [hx0, sq_nonneg x, pow_nonneg hx0 3, pow_nonneg hx0 4,
      pow_nonneg hx0 5]
  have houter : (6283 / 500 : ℝ) ≤ 4 * Real.pi := by
    linarith only [Real.pi_gt_d4]
  have hb := thetaCuspFirstLiouvilleIntervalCertificate_le_gibbs hj hx
  have hb0 : 0 ≤
      (3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificate j *
        thetaCuspExpTaylorFive
          (thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8 - x)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (thetaCuspFirstLiouvilleEndpointCertificate_pos hj).le)
      (thetaCuspExpTaylorFive_nonneg (mul_nonneg
        (thetaCuspFirstLiouvilleRateSlope_pos hj).le (by
          push_cast at hx ⊢
          linarith [hx.2])))
  have hgibbs0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hactualInner0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 :=
    hinner0.trans hinner
  rw [thetaCuspFirstAtomFourthIntervalCertificate,
    thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    (6283 / 500 : ℝ) * (3 / 70) * thetaCuspFirstLiouvilleEndpointCertificate j *
          x ^ (4 : ℕ) *
          ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          thetaCuspExpTaylorFive
            (thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8 - x)) =
        (6283 / 500 : ℝ) * x ^ (4 : ℕ) *
          ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          ((3 / 70 : ℝ) * thetaCuspFirstLiouvilleEndpointCertificate j *
            thetaCuspExpTaylorFive
              (thetaCuspFirstLiouvilleRateSlope j * (((j + 1 : ℕ) : ℝ) / 8 - x))) := by
      ring
    _ ≤ (6283 / 500 : ℝ) * x ^ (4 : ℕ) *
          ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 4)) hinner0)
    _ ≤ (6283 / 500 : ℝ) * x ^ (4 : ℕ) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by norm_num) (pow_nonneg hx0 4))) hgibbs0
    _ ≤ (4 * Real.pi) * x ^ (4 : ℕ) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 4)) hactualInner0)
        hgibbs0
    _ = 2 * (x ^ (4 : ℕ) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) := by ring

theorem thetaCuspExpTaylorFive_eq_sum (u : ℝ) :
    thetaCuspExpTaylorFive u =
      ∑ n ∈ Finset.range 6, u ^ n / (n.factorial : ℝ) := by
  norm_num [thetaCuspExpTaylorFive, Finset.sum_range_succ]

theorem thetaCuspExpTaylorThree_eq_sum (u : ℝ) :
    thetaCuspExpTaylorThree u =
      ∑ n ∈ Finset.range 4, u ^ n / (n.factorial : ℝ) := by
  norm_num [thetaCuspExpTaylorThree, Finset.sum_range_succ]

/-- Exact rational integral of `x^r (b-x)^m` over `[a,b]`. -/
def thetaCuspIntervalPowSubMass (r m : ℕ) (a b : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ (q + m) * b ^ q * (m.choose q : ℝ) *
      ((b ^ (r + (m - q) + 1) - a ^ (r + (m - q) + 1)) /
        (r + (m - q) + 1 : ℕ))

theorem intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass
    (r m : ℕ) (a b : ℝ) :
    (∫ x in a..b, x ^ r * (b - x) ^ m) =
      thetaCuspIntervalPowSubMass r m a b := by
  rw [show (fun x : ℝ => x ^ r * (b - x) ^ m) = fun x : ℝ =>
      ∑ q ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ (q + m) * b ^ q * (m.choose q : ℝ)) *
          x ^ (r + (m - q)) by
    funext x
    rw [sub_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [pow_add]
    ring]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  · intro q hq
    exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable a b

/-- Exact algebraic mass of the Taylor shape before the endpoint and outer constants. -/
def thetaCuspFirstAtomFourthTaylorMass (a b k : ℝ) : ℝ :=
  (6283 / 1000 : ℝ) *
      ∑ n ∈ Finset.range 6,
        ((2 : ℝ) ^ n / (n.factorial : ℝ)) *
          ∑ m ∈ Finset.range 6,
            (k ^ m / (m.factorial : ℝ)) *
              thetaCuspIntervalPowSubMass (4 + n) m a b -
    3 * ∑ m ∈ Finset.range 6,
      (k ^ m / (m.factorial : ℝ)) * thetaCuspIntervalPowSubMass 4 m a b

theorem intervalIntegral_thetaCuspFirstAtomFourthTaylorShape_eq_mass
    (a b k : ℝ) :
    (∫ x in a..b,
      x ^ (4 : ℕ) * ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
        thetaCuspExpTaylorFive (k * (b - x))) =
      thetaCuspFirstAtomFourthTaylorMass a b k := by
  have hfun :
      (fun x : ℝ =>
        x ^ (4 : ℕ) * ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
          thetaCuspExpTaylorFive (k * (b - x))) =
      fun x : ℝ =>
        (6283 / 1000 : ℝ) *
            ∑ n ∈ Finset.range 6,
              ∑ m ∈ Finset.range 6,
                (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
                  (k ^ m / (m.factorial : ℝ))) *
                    (x ^ (4 + n) * (b - x) ^ m) -
          3 * ∑ m ∈ Finset.range 6,
            (k ^ m / (m.factorial : ℝ)) * (x ^ (4 : ℕ) * (b - x) ^ m) := by
    funext x
    rw [thetaCuspExpTaylorFive_eq_sum (2 * x),
      thetaCuspExpTaylorFive_eq_sum (k * (b - x))]
    simp_rw [mul_pow, pow_add]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_sub, sub_mul]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    congr 3 <;> ring
    funext y
    congr 2 ; ring
    funext n
    ring
  rw [hfun]
  rw [intervalIntegral.integral_sub
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      (6283 / 1000 : ℝ) *
        ∑ n ∈ Finset.range 6, ∑ m ∈ Finset.range 6,
          (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
            (k ^ m / (m.factorial : ℝ))) *
              (x ^ (4 + n) * (b - x) ^ m))).intervalIntegrable a b)
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      3 * ∑ m ∈ Finset.range 6,
        (k ^ m / (m.factorial : ℝ)) * (x ^ (4 : ℕ) * (b - x) ^ m))).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply congrArg₂ (· - ·)
    · apply congrArg ((6283 / 1000 : ℝ) * ·)
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass]
        ring
      · intro m hm
        exact (by fun_prop : Continuous (fun x : ℝ =>
          (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
            (k ^ m / (m.factorial : ℝ))) *
              (x ^ (4 + n) * (b - x) ^ m))).intervalIntegrable a b
    · rw [intervalIntegral.integral_finsetSum]
      · apply congrArg (3 * ·)
        apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass]
      · intro m hm
        exact (by fun_prop : Continuous (fun x : ℝ =>
          (k ^ m / (m.factorial : ℝ)) *
            (x ^ (4 : ℕ) * (b - x) ^ m))).intervalIntegrable a b
  · intro n hn
    exact (by fun_prop : Continuous (fun x : ℝ =>
      ∑ m ∈ Finset.range 6,
        (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
          (k ^ m / (m.factorial : ℝ))) *
            (x ^ (4 + n) * (b - x) ^ m))).intervalIntegrable a b

def thetaCuspFirstAtomFourthIntervalMass (j : ℕ) : ℝ :=
  (6283 / 500 : ℝ) * (3 / 70) *
    thetaCuspFirstAtomFourthTaylorMass
      ((j : ℝ) / 8) (((j + 1 : ℕ) : ℝ) / 8)
      (thetaCuspFirstLiouvilleRateSlope j)

theorem intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass
    (j : ℕ) :
    (∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate j x) =
      thetaCuspFirstLiouvilleEndpointCertificate j *
        thetaCuspFirstAtomFourthIntervalMass j := by
  rw [show (fun x : ℝ => thetaCuspFirstAtomFourthIntervalCertificate j x) =
      fun x : ℝ =>
        ((6283 / 500 : ℝ) * (3 / 70) * thetaCuspFirstLiouvilleEndpointCertificate j) *
          (x ^ (4 : ℕ) * ((6283 / 1000 : ℝ) * thetaCuspExpTaylorFive (2 * x) - 3) *
            thetaCuspExpTaylorFive
              (thetaCuspFirstLiouvilleRateSlope j *
                ((((j + 1 : ℕ) : ℝ) / 8) - x))) by
    funext x
    rw [thetaCuspFirstAtomFourthIntervalCertificate]
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_thetaCuspFirstAtomFourthTaylorShape_eq_mass]
  rw [thetaCuspFirstAtomFourthIntervalMass]
  ring

/-! Each interval certificate is an exact rational number, evaluated once below; the weaker
per-interval bounds and the seven-interval sum follow from these evaluations. -/

/-- Rational lower bound for the interval certificate on `[0/8, 1/8]`, from the
exact evaluation of its rational mass. -/
theorem nineteen_div_twoMillion_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_zero :
    (19 / 2000000 : ℝ) < ∫ x in ((0 : ℕ) : ℝ) / 8..(((0 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 0 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- Rational lower bound for the interval certificate on `[1/8, 2/8]`, from the
exact evaluation of its rational mass. -/
theorem twentyOne_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_one :
    (21 / 100000 : ℝ) < ∫ x in ((1 : ℕ) : ℝ) / 8..(((1 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 1 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- Rational lower bound for the interval certificate on `[2/8, 3/8]`, from the
exact evaluation of its rational mass. -/
theorem three_div_fourThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_two :
    (3 / 4000 : ℝ) < ∫ x in ((2 : ℕ) : ℝ) / 8..(((2 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 2 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- Rational lower bound for the interval certificate on `[3/8, 4/8]`, from the
exact evaluation of its rational mass. -/
theorem ninetyNine_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_three :
    (99 / 100000 : ℝ) < ∫ x in ((3 : ℕ) : ℝ) / 8..(((3 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 3 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- Rational lower bound for the interval certificate on `[4/8, 5/8]`, from the
exact evaluation of its rational mass. -/
theorem fiftyNine_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_four :
    (59 / 100000 : ℝ) < ∫ x in ((4 : ℕ) : ℝ) / 8..(((4 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 4 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- Rational lower bound for the interval certificate on `[5/8, 6/8]`, from the
exact evaluation of its rational mass. -/
theorem four_div_twentyFiveThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_five :
    (4 / 25000 : ℝ) < ∫ x in ((5 : ℕ) : ℝ) / 8..(((5 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 5 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

/-- Rational lower bound for the interval certificate on `[6/8, 7/8]`, from the
exact evaluation of its rational mass. -/
theorem seventeen_div_oneMillion_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_six :
    (17 / 1000000 : ℝ) < ∫ x in ((6 : ℕ) : ℝ) / 8..(((6 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 6 x := by
  rw [intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_eq_mass]
  norm_num [thetaCuspFirstAtomFourthIntervalMass,
    thetaCuspFirstAtomFourthTaylorMass, thetaCuspIntervalPowSubMass,
    thetaCuspFirstLiouvilleRateSlope,
    thetaCuspFirstLiouvilleEndpointCertificate,
    thetaCuspFirstLiouvilleRateMajorant, thetaCuspQuarterExpChord,
    thetaCuspQuarterExpMajorant, eval_expNegTruncPoly, Nat.choose,
    Finset.sum_range_succ]

theorem one_div_oneMillion_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_zero :
    (1 / 1000000 : ℝ) < ∫ x in ((0 : ℕ) : ℝ) / 8..(((0 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 0 x :=
  (by norm_num : (1 / 1000000 : ℝ) < 19 / 2000000).trans
    nineteen_div_twoMillion_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_zero

theorem nineteen_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_one :
    (19 / 100000 : ℝ) < ∫ x in ((1 : ℕ) : ℝ) / 8..(((1 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 1 x :=
  (by norm_num : (19 / 100000 : ℝ) < 21 / 100000).trans
    twentyOne_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_one

theorem seventeen_div_twentyFiveThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_two :
    (17 / 25000 : ℝ) < ∫ x in ((2 : ℕ) : ℝ) / 8..(((2 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 2 x :=
  (by norm_num : (17 / 25000 : ℝ) < 3 / 4000).trans
    three_div_fourThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_two

theorem twentyOne_div_twentyFiveThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_three :
    (21 / 25000 : ℝ) < ∫ x in ((3 : ℕ) : ℝ) / 8..(((3 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 3 x :=
  (by norm_num : (21 / 25000 : ℝ) < 99 / 100000).trans
    ninetyNine_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_three

theorem eleven_div_twentyFiveThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_four :
    (11 / 25000 : ℝ) < ∫ x in ((4 : ℕ) : ℝ) / 8..(((4 + 1 : ℕ) : ℝ) / 8),
      thetaCuspFirstAtomFourthIntervalCertificate 4 x :=
  (by norm_num : (11 / 25000 : ℝ) < 59 / 100000).trans
    fiftyNine_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_four

/-- The seven exact rational interval certificates clear the stronger `269/100000` threshold. -/
theorem twoHundredSixtyNine_div_oneHundredThousand_lt_sum_thetaCuspFirstAtomFourthIntervalCertificate :
    (269 / 100000 : ℝ) <
      ∑ j ∈ Finset.range 7,
        ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8),
          thetaCuspFirstAtomFourthIntervalCertificate j x := by
  have h0 := nineteen_div_twoMillion_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_zero
  have h1 := twentyOne_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_one
  have h2 := three_div_fourThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_two
  have h3 := ninetyNine_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_three
  have h4 := fiftyNine_div_oneHundredThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_four
  have h5 := four_div_twentyFiveThousand_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_five
  have h6 := seventeen_div_oneMillion_lt_intervalIntegral_thetaCuspFirstAtomFourthIntervalCertificate_six
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  linarith

/-- **Unconditional dominant-atom fourth-moment floor.** -/
theorem twoHundredSixtyNine_div_oneHundredThousand_lt_thetaCuspAtomRawEvenMoment_two_one :
    (269 / 100000 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 := by
  let f : ℝ → ℝ := fun x => 2 * (x ^ (4 : ℕ) * thetaCuspSourceTerm x 1)
  have hfcont : Continuous f := by
    dsimp only [f]
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspSourceTerm 2 1).const_mul 2
    apply h.congr
    filter_upwards [] with x
    dsimp only [f]
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (by norm_num) <|
      mul_nonneg (pow_nonneg hx.le _) (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hsegment (j : ℕ) (hj : j < 7) :
      (∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8),
          thetaCuspFirstAtomFourthIntervalCertificate j x) ≤
        ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8), f x := by
    apply intervalIntegral.integral_mono_on
    · push_cast
      linarith
    · have hcertcont : Continuous
          (thetaCuspFirstAtomFourthIntervalCertificate j) := by
        unfold thetaCuspFirstAtomFourthIntervalCertificate thetaCuspExpTaylorFive
        fun_prop
      exact hcertcont.intervalIntegrable _ _
    · exact hfcont.intervalIntegrable _ _
    · intro x hx
      exact thetaCuspFirstAtomFourthIntervalCertificate_le_density hj hx
  have hsum :
      (∑ j ∈ Finset.range 7,
          ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8),
            thetaCuspFirstAtomFourthIntervalCertificate j x) ≤
        ∑ j ∈ Finset.range 7,
          ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8), f x := by
    exact Finset.sum_le_sum fun j hj => hsegment j (Finset.mem_range.mp hj)
  have hjoin :
      (∑ j ∈ Finset.range 7,
          ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8), f x) =
        ∫ x in (0 : ℝ)..7 / 8, f x := by
    norm_num [Finset.sum_range_succ]
    calc
      ((((((∫ x in (0 : ℝ)..1 / 8, f x) + ∫ x in (1 / 8 : ℝ)..1 / 4, f x) +
                  ∫ x in (1 / 4 : ℝ)..3 / 8, f x) +
                ∫ x in (3 / 8 : ℝ)..1 / 2, f x) +
              ∫ x in (1 / 2 : ℝ)..5 / 8, f x) +
            ∫ x in (5 / 8 : ℝ)..3 / 4, f x) +
          ∫ x in (3 / 4 : ℝ)..7 / 8, f x =
          (((((∫ x in (0 : ℝ)..1 / 4, f x) +
                  ∫ x in (1 / 4 : ℝ)..3 / 8, f x) +
                ∫ x in (3 / 8 : ℝ)..1 / 2, f x) +
              ∫ x in (1 / 2 : ℝ)..5 / 8, f x) +
            ∫ x in (5 / 8 : ℝ)..3 / 4, f x) +
          ∫ x in (3 / 4 : ℝ)..7 / 8, f x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hfcont.intervalIntegrable 0 (1 / 8))
          (hfcont.intervalIntegrable (1 / 8) (1 / 4))]
      _ = ((((∫ x in (0 : ℝ)..3 / 8, f x) +
                ∫ x in (3 / 8 : ℝ)..1 / 2, f x) +
              ∫ x in (1 / 2 : ℝ)..5 / 8, f x) +
            ∫ x in (5 / 8 : ℝ)..3 / 4, f x) +
          ∫ x in (3 / 4 : ℝ)..7 / 8, f x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hfcont.intervalIntegrable 0 (1 / 4))
          (hfcont.intervalIntegrable (1 / 4) (3 / 8))]
      _ = (((∫ x in (0 : ℝ)..1 / 2, f x) +
              ∫ x in (1 / 2 : ℝ)..5 / 8, f x) +
            ∫ x in (5 / 8 : ℝ)..3 / 4, f x) +
          ∫ x in (3 / 4 : ℝ)..7 / 8, f x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hfcont.intervalIntegrable 0 (3 / 8))
          (hfcont.intervalIntegrable (3 / 8) (1 / 2))]
      _ = ((∫ x in (0 : ℝ)..5 / 8, f x) +
            ∫ x in (5 / 8 : ℝ)..3 / 4, f x) +
          ∫ x in (3 / 4 : ℝ)..7 / 8, f x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hfcont.intervalIntegrable 0 (1 / 2))
          (hfcont.intervalIntegrable (1 / 2) (5 / 8))]
      _ = (∫ x in (0 : ℝ)..3 / 4, f x) +
          ∫ x in (3 / 4 : ℝ)..7 / 8, f x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hfcont.intervalIntegrable 0 (5 / 8))
          (hfcont.intervalIntegrable (5 / 8) (3 / 4))]
      _ = ∫ x in (0 : ℝ)..7 / 8, f x := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hfcont.intervalIntegrable 0 (3 / 4))
          (hfcont.intervalIntegrable (3 / 4) (7 / 8))]
  have hwindow : (∫ x in (0 : ℝ)..7 / 8, f x) ≤ ∫ x in Ioi 0, f x := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    exact setIntegral_mono_set hfint hfnonneg
      (Filter.Eventually.of_forall fun x hx => hx.1)
  have hraw : (∫ x in Ioi 0, f x) = thetaCuspAtomRawEvenMoment 2 1 := by
    rw [thetaCuspAtomRawEvenMoment]
    dsimp only [f]
    rw [← integral_const_mul]
  have hcert :=
    twoHundredSixtyNine_div_oneHundredThousand_lt_sum_thetaCuspFirstAtomFourthIntervalCertificate
  calc
    (269 / 100000 : ℝ) <
        ∑ j ∈ Finset.range 7,
          ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8),
            thetaCuspFirstAtomFourthIntervalCertificate j x := hcert
    _ ≤ ∑ j ∈ Finset.range 7,
          ∫ x in (j : ℝ) / 8..(((j + 1 : ℕ) : ℝ) / 8), f x := hsum
    _ = ∫ x in (0 : ℝ)..7 / 8, f x := hjoin
    _ ≤ ∫ x in Ioi 0, f x := hwindow
    _ = thetaCuspAtomRawEvenMoment 2 1 := hraw

/-- Compatibility form of the earlier seven-interval floor. -/
theorem twoHundredSixtyThree_div_oneHundredThousand_lt_thetaCuspAtomRawEvenMoment_two_one :
    (263 / 100000 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 := by
  linarith only [twoHundredSixtyNine_div_oneHundredThousand_lt_thetaCuspAtomRawEvenMoment_two_one]

/-- Compatibility form of the earlier six-interval floor. -/
theorem three_div_oneThousandTwoHundredFifty_lt_thetaCuspAtomRawEvenMoment_two_one :
    (3 / 1250 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 := by
  linarith only [twoHundredSixtyThree_div_oneHundredThousand_lt_thetaCuspAtomRawEvenMoment_two_one]

/-- Compatibility form of the earlier five-interval floor. -/
theorem twoThousandOneHundredFiftyOne_div_oneMillion_lt_thetaCuspAtomRawEvenMoment_two_one :
    (2151 / 1000000 : ℝ) < thetaCuspAtomRawEvenMoment 2 1 := by
  linarith only [three_div_oneThousandTwoHundredFifty_lt_thetaCuspAtomRawEvenMoment_two_one]

end

end RHTower
