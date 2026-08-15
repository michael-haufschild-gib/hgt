import GaloisForLFunctions.RHTower.PrimeArchThetaThirdCumulantLikelihoodTailEnvelope
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentSixteenthFloor
import GaloisForLFunctions.RHTower.ThetaSingleGibbsLikelihoodSingleLossClosure

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

def thetaCuspThirtySecondExpLower : ℝ := 51587 / 50000
def thetaCuspThirtySecondExpUpper : ℝ := 4127 / 4000

def thetaCuspSixtyFourthExpUpperChord (j : ℕ) (x : ℝ) : ℝ :=
  let t : ℝ := 64 * x - j
  (1 - t) * thetaCuspThirtySecondExpUpper ^ j +
    t * thetaCuspThirtySecondExpUpper ^ (j + 1)

def thetaCuspSixtyFourthExpLowerTangent (j : ℕ) (x : ℝ) : ℝ :=
  thetaCuspThirtySecondExpLower ^ j * (1 + 2 * (x - (j : ℝ) / 64))

def thetaCuspFirstRateUpper64 (j : ℕ) (x : ℝ) : ℝ :=
  (3.14159265358979323847 : ℝ) *
      (thetaCuspSixtyFourthExpUpperChord j x - 1) - 5 * x / 2

def thetaCuspFirstRateUpperSlope64 (j : ℕ) : ℝ :=
  (3.14159265358979323847 : ℝ) * 64 *
      (thetaCuspThirtySecondExpUpper ^ (j + 1) -
        thetaCuspThirtySecondExpUpper ^ j) - 5 / 2

def thetaCuspFirstRateLower64 (j : ℕ) (x : ℝ) : ℝ :=
  let a : ℝ := (j : ℝ) / 64
  let z : ℝ := (3.14159265358979323846 : ℝ) *
      (thetaCuspThirtySecondExpLower ^ j - 1) - 5 * a / 2
  let k : ℝ := 2 * (3.14159265358979323846 : ℝ) *
      thetaCuspThirtySecondExpLower ^ j - 5 / 2
  z + k * (x - a)

def thetaCuspFirstRateLowerEndpoint64 (j : ℕ) : ℝ :=
  (3.14159265358979323846 : ℝ) *
      (thetaCuspThirtySecondExpLower ^ j - 1) -
    5 * ((j : ℝ) / 64) / 2

def thetaCuspFirstRateLowerSlope64 (j : ℕ) : ℝ :=
  2 * (3.14159265358979323846 : ℝ) *
      thetaCuspThirtySecondExpLower ^ j - 5 / 2

def thetaCuspFirstRateUpperEndpointCertificate64 (j : ℕ) : ℝ :=
  (expNegTruncPoly 64).eval
    (thetaCuspFirstRateUpper64 j (((j + 1 : ℕ) : ℝ) / 64))

def thetaCuspFirstRateLowerEndpointCertificate64 (j : ℕ) : ℝ :=
  (expNegTruncPoly 65).eval (thetaCuspFirstRateLowerEndpoint64 j)

theorem thetaCuspThirtySecondExpLower_lt_exp :
    thetaCuspThirtySecondExpLower < Real.exp (1 / 32 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 32 by norm_num) 4
  norm_num [Finset.sum_range_succ, thetaCuspThirtySecondExpLower] at h ⊢
  linarith

theorem exp_lt_thetaCuspThirtySecondExpUpper :
    Real.exp (1 / 32 : ℝ) < thetaCuspThirtySecondExpUpper := by
  rw [thetaCuspThirtySecondExpUpper]
  by_contra h
  have hle : (4127 / 4000 : ℝ) ≤ Real.exp (1 / 32 : ℝ) := le_of_not_gt h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4127 / 4000) hle 32
  have heq : Real.exp (1 / 32 : ℝ) ^ 32 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq] at hp
  have hu : Real.exp 1 < (4127 / 4000 : ℝ) ^ 32 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  linarith

theorem thetaCuspThirtySecondExpLower_pow_le_exp (j : ℕ) :
    thetaCuspThirtySecondExpLower ^ j ≤ Real.exp ((j : ℝ) / 32) := by
  rw [show (j : ℝ) / 32 = (j : ℕ) * (1 / 32 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num [thetaCuspThirtySecondExpLower])
    thetaCuspThirtySecondExpLower_lt_exp.le j

theorem exp_le_thetaCuspThirtySecondExpUpper_pow (j : ℕ) :
    Real.exp ((j : ℝ) / 32) ≤ thetaCuspThirtySecondExpUpper ^ j := by
  rw [show (j : ℝ) / 32 = (j : ℕ) * (1 / 32 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le
    exp_lt_thetaCuspThirtySecondExpUpper.le j

theorem exp_two_mul_le_thetaCuspSixtyFourthExpUpperChord
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 64)) :
    Real.exp (2 * x) ≤ thetaCuspSixtyFourthExpUpperChord j x := by
  let t : ℝ := 64 * x - j
  have ht0 : 0 ≤ t := by dsimp only [t]; push_cast at hx ⊢; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; push_cast at hx ⊢; linarith
  have hconv := convexOn_exp.2
    (Set.mem_univ ((j : ℝ) / 32))
    (Set.mem_univ (((j + 1 : ℕ) : ℝ) / 32))
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  have harg :
      (1 - t) * ((j : ℝ) / 32) +
          t * (((j + 1 : ℕ) : ℝ) / 32) = 2 * x := by
    dsimp only [t]
    push_cast
    ring
  simp only [smul_eq_mul] at hconv
  rw [harg] at hconv
  have hj := exp_le_thetaCuspThirtySecondExpUpper_pow j
  have hj1 := exp_le_thetaCuspThirtySecondExpUpper_pow (j + 1)
  calc
    Real.exp (2 * x) ≤
        (1 - t) * Real.exp ((j : ℝ) / 32) +
          t * Real.exp (((j + 1 : ℕ) : ℝ) / 32) := hconv
    _ ≤ (1 - t) * thetaCuspThirtySecondExpUpper ^ j +
          t * thetaCuspThirtySecondExpUpper ^ (j + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hj1 ht0)
    _ = thetaCuspSixtyFourthExpUpperChord j x := by
      simp only [thetaCuspSixtyFourthExpUpperChord, t]

theorem thetaCuspSixtyFourthExpLowerTangent_le_exp_two_mul
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x) :
    thetaCuspSixtyFourthExpLowerTangent j x ≤ Real.exp (2 * x) := by
  let a : ℝ := (j : ℝ) / 64
  let y : ℝ := 2 * (x - a)
  have hy : 0 ≤ y := by dsimp only [y, a]; linarith
  have hlin : 1 + y ≤ Real.exp y := by
    simpa only [add_comm] using Real.add_one_le_exp y
  have hgrid := thetaCuspThirtySecondExpLower_pow_le_exp j
  have hgrid0 : 0 ≤ thetaCuspThirtySecondExpLower ^ j := by
    rw [thetaCuspThirtySecondExpLower]
    positivity
  have hmul := mul_le_mul hgrid hlin (by linarith) (Real.exp_pos _).le
  rw [show Real.exp (2 * x) = Real.exp ((j : ℝ) / 32) * Real.exp y by
    rw [← Real.exp_add]
    congr 1
    dsimp only [y, a]
    ring]
  simpa only [thetaCuspSixtyFourthExpLowerTangent, y, a] using hmul

theorem thetaCuspFirstLiouvilleRate_le_upper64
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 64)) :
    thetaCuspFirstLiouvilleRate x ≤ thetaCuspFirstRateUpper64 j x := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
  have hchord := exp_two_mul_le_thetaCuspSixtyFourthExpUpperChord hx
  have hchord0 : 0 ≤ thetaCuspSixtyFourthExpUpperChord j x - 1 := by
    have := Real.one_le_exp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)
    linarith
  rw [thetaCuspFirstLiouvilleRate, thetaCuspFirstRateUpper64]
  calc
    Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2 ≤
        Real.pi * (thetaCuspSixtyFourthExpUpperChord j x - 1) - 5 * x / 2 := by
      gcongr
    _ ≤ (3.14159265358979323847 : ℝ) *
          (thetaCuspSixtyFourthExpUpperChord j x - 1) - 5 * x / 2 := by
      gcongr
      exact Real.pi_lt_d20.le

theorem thetaCuspFirstRateLower64_le_liouvilleRate
    {j : ℕ} {x : ℝ} (hx : (j : ℝ) / 64 ≤ x) :
    thetaCuspFirstRateLower64 j x ≤ thetaCuspFirstLiouvilleRate x := by
  let a : ℝ := (j : ℝ) / 64
  let E : ℝ := thetaCuspThirtySecondExpLower ^ j
  have hE0 : 0 ≤ E := by
    dsimp only [E, thetaCuspThirtySecondExpLower]
    positivity
  have hdx : 0 ≤ x - a := by dsimp only [a]; linarith
  have hEtan := thetaCuspSixtyFourthExpLowerTangent_le_exp_two_mul hx
  have hshape0 : 0 ≤ E * (1 + 2 * (x - a)) - 1 := by
    have hE1 : 1 ≤ E := by
      dsimp only [E, thetaCuspThirtySecondExpLower]
      exact one_le_pow₀ (by norm_num)
    nlinarith
  rw [thetaCuspFirstLiouvilleRate, thetaCuspFirstRateLower64]
  dsimp only [a, E] at *
  calc
    (3.14159265358979323846 : ℝ) *
          (thetaCuspThirtySecondExpLower ^ j - 1) - 5 * ((j : ℝ) / 64) / 2 +
        (2 * (3.14159265358979323846 : ℝ) *
            thetaCuspThirtySecondExpLower ^ j - 5 / 2) *
          (x - (j : ℝ) / 64) =
        (3.14159265358979323846 : ℝ) *
          (thetaCuspThirtySecondExpLower ^ j *
            (1 + 2 * (x - (j : ℝ) / 64)) - 1) - 5 * x / 2 := by ring
    _ ≤ Real.pi *
          (thetaCuspThirtySecondExpLower ^ j *
            (1 + 2 * (x - (j : ℝ) / 64)) - 1) - 5 * x / 2 := by
      gcongr
      exact Real.pi_gt_d20.le
    _ ≤ Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2 := by
      have hEtan' : thetaCuspThirtySecondExpLower ^ j *
          (1 + 2 * (x - (j : ℝ) / 64)) ≤ Real.exp (2 * x) := by
        simpa only [thetaCuspSixtyFourthExpLowerTangent] using hEtan
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hEtan' 1) Real.pi_pos.le)
        (5 * x / 2)

theorem thetaCuspFirstRateUpper64_affine (j : ℕ) (x : ℝ) :
    thetaCuspFirstRateUpper64 j x =
      thetaCuspFirstRateUpper64 j (((j + 1 : ℕ) : ℝ) / 64) -
        thetaCuspFirstRateUpperSlope64 j *
          (((j + 1 : ℕ) : ℝ) / 64 - x) := by
  simp only [thetaCuspFirstRateUpper64, thetaCuspFirstRateUpperSlope64,
    thetaCuspSixtyFourthExpUpperChord, thetaCuspThirtySecondExpUpper]
  push_cast
  ring

theorem thetaCuspFirstRateLower64_eq_endpoint_slope (j : ℕ) (x : ℝ) :
    thetaCuspFirstRateLower64 j x = thetaCuspFirstRateLowerEndpoint64 j +
      thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64) := by
  rfl

theorem thetaCuspFirstRateUpperSlope64_pos (j : ℕ) :
    0 < thetaCuspFirstRateUpperSlope64 j := by
  have hpow : 1 ≤ thetaCuspThirtySecondExpUpper ^ j := by
    exact one_le_pow₀ (by norm_num [thetaCuspThirtySecondExpUpper])
  rw [thetaCuspFirstRateUpperSlope64]
  have heq : thetaCuspThirtySecondExpUpper ^ (j + 1) -
      thetaCuspThirtySecondExpUpper ^ j =
        thetaCuspThirtySecondExpUpper ^ j *
          (thetaCuspThirtySecondExpUpper - 1) := by rw [pow_succ]; ring
  rw [heq]
  norm_num [thetaCuspThirtySecondExpUpper] at *
  nlinarith

theorem thetaCuspFirstRateLowerSlope64_pos (j : ℕ) :
    0 < thetaCuspFirstRateLowerSlope64 j := by
  have hpow : 1 ≤ thetaCuspThirtySecondExpLower ^ j := by
    exact one_le_pow₀ (by norm_num [thetaCuspThirtySecondExpLower])
  rw [thetaCuspFirstRateLowerSlope64]
  norm_num at *
  nlinarith

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem thetaCuspFirstRateUpperEndpointCertificate64_pos
    {j : ℕ} (hj : j < 56) :
    0 < thetaCuspFirstRateUpperEndpointCertificate64 j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstRateUpperEndpointCertificate64,
      thetaCuspFirstRateUpper64, thetaCuspSixtyFourthExpUpperChord,
      thetaCuspThirtySecondExpUpper, eval_expNegTruncPoly,
      Finset.sum_range_succ]

theorem thetaCuspFirstRateUpperEndpointCertificate64_lt_exp
    {j : ℕ} (hj : j < 56) :
    thetaCuspFirstRateUpperEndpointCertificate64 j <
      Real.exp (-thetaCuspFirstRateUpper64 j (((j + 1 : ℕ) : ℝ) / 64)) := by
  have hz : 0 < thetaCuspFirstRateUpper64 j (((j + 1 : ℕ) : ℝ) / 64) := by
    interval_cases j <;>
      norm_num [thetaCuspFirstRateUpper64,
        thetaCuspSixtyFourthExpUpperChord, thetaCuspThirtySecondExpUpper]
  have h := expNegTruncPoly_sub_exp_oriented_pos (m := 64) (by norm_num) hz
  norm_num at h
  simpa only [thetaCuspFirstRateUpperEndpointCertificate64,
    Nat.cast_add, Nat.cast_one] using h

theorem thetaCuspFirstRateLowerEndpoint64_nonneg
    {j : ℕ} (hj : j ≤ 56) :
    0 ≤ thetaCuspFirstRateLowerEndpoint64 j := by
  interval_cases j <;>
    norm_num [thetaCuspFirstRateLowerEndpoint64, thetaCuspThirtySecondExpLower]

theorem exp_neg_le_thetaCuspFirstRateLowerEndpointCertificate64
    {j : ℕ} (hj : j ≤ 56) :
    Real.exp (-thetaCuspFirstRateLowerEndpoint64 j) ≤
      thetaCuspFirstRateLowerEndpointCertificate64 j := by
  have hz := thetaCuspFirstRateLowerEndpoint64_nonneg hj
  rcases hz.eq_or_lt with hz0 | hzpos
  · have hz0' : thetaCuspFirstRateLowerEndpoint64 j = 0 := hz0.symm
    rw [hz0']
    norm_num [thetaCuspFirstRateLowerEndpointCertificate64,
      eval_expNegTruncPoly, Finset.sum_range_succ, hz0']
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 65) (by norm_num) hzpos
    norm_num at h
    simpa only [thetaCuspFirstRateLowerEndpointCertificate64] using h.le

theorem exp_neg_le_expNegTruncPoly_nine {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (expNegTruncPoly 9).eval t := by
  rcases ht.eq_or_lt with hzero | hpos
  · rw [← hzero]
    norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos
      (m := 9) (by norm_num) hpos
    norm_num at h
    exact h.le

theorem thetaCuspFirstGibbsLower64_le
    {j : ℕ} (hj : j < 56) {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 64)) :
    (0.0432139182637 : ℝ) * thetaCuspFirstRateUpperEndpointCertificate64 j *
        thetaCuspExpTaylorFive
          (thetaCuspFirstRateUpperSlope64 j *
            (((j + 1 : ℕ) : ℝ) / 64 - x)) ≤
      thetaCuspLiouvilleGibbsAtom 1 x := by
  let b : ℝ := ((j + 1 : ℕ) : ℝ) / 64
  let z : ℝ := thetaCuspFirstRateUpper64 j b
  let k : ℝ := thetaCuspFirstRateUpperSlope64 j
  let u : ℝ := k * (b - x)
  have hk : 0 < k := by simpa only [k] using thetaCuspFirstRateUpperSlope64_pos j
  have hxb : 0 ≤ b - x := by dsimp only [b]; linarith
  have hu : 0 ≤ u := mul_nonneg hk.le hxb
  have hrate := thetaCuspFirstLiouvilleRate_le_upper64 hx
  have haffine := thetaCuspFirstRateUpper64_affine j x
  have hrate' : thetaCuspFirstLiouvilleRate x ≤ z - u := by
    dsimp only [z, u, k, b]
    rw [← haffine]
    exact hrate
  have hexpRate : Real.exp (-z) * Real.exp u ≤
      Real.exp (-thetaCuspFirstLiouvilleRate x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hP := thetaCuspFirstRateUpperEndpointCertificate64_lt_exp hj
  have hP0 := thetaCuspFirstRateUpperEndpointCertificate64_pos hj
  have hT := thetaCuspExpTaylorFive_le_exp hu
  have hT0 := thetaCuspExpTaylorFive_nonneg hu
  have hPT : thetaCuspFirstRateUpperEndpointCertificate64 j *
      thetaCuspExpTaylorFive u ≤ Real.exp (-z) * Real.exp u := by
    exact mul_le_mul hP.le hT hT0 (Real.exp_pos _).le
  rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    (0.0432139182637 : ℝ) * thetaCuspFirstRateUpperEndpointCertificate64 j *
          thetaCuspExpTaylorFive
            (thetaCuspFirstRateUpperSlope64 j *
              (((j + 1 : ℕ) : ℝ) / 64 - x)) =
        (0.0432139182637 : ℝ) *
          (thetaCuspFirstRateUpperEndpointCertificate64 j *
            thetaCuspExpTaylorFive u) := by
      dsimp only [u, k, b]
      ring
    _ ≤ Real.exp (-Real.pi) *
          (thetaCuspFirstRateUpperEndpointCertificate64 j *
            thetaCuspExpTaylorFive u) := by
      exact mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_lower
        (mul_nonneg hP0.le hT0)
    _ ≤ Real.exp (-Real.pi) * (Real.exp (-z) * Real.exp u) := by
      exact mul_le_mul_of_nonneg_left hPT (Real.exp_pos _).le
    _ ≤ Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x) := by
      exact mul_le_mul_of_nonneg_left hexpRate (Real.exp_pos _).le

theorem thetaCuspFirstGibbs_le_upper64
    {j : ℕ} (hj : j < 56) {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 64)) :
    thetaCuspLiouvilleGibbsAtom 1 x ≤
      (0.0432139182638 : ℝ) * thetaCuspFirstRateLowerEndpointCertificate64 j *
        (expNegTruncPoly 9).eval
          (thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64)) := by
  let a : ℝ := (j : ℝ) / 64
  let z : ℝ := thetaCuspFirstRateLowerEndpoint64 j
  let k : ℝ := thetaCuspFirstRateLowerSlope64 j
  let t : ℝ := k * (x - a)
  have hk : 0 < k := by simpa only [k] using thetaCuspFirstRateLowerSlope64_pos j
  have hxa : 0 ≤ x - a := by dsimp only [a]; linarith
  have ht : 0 ≤ t := mul_nonneg hk.le hxa
  have hrate := thetaCuspFirstRateLower64_le_liouvilleRate hx.1
  have haffine := thetaCuspFirstRateLower64_eq_endpoint_slope j x
  have hrate' : z + t ≤ thetaCuspFirstLiouvilleRate x := by
    dsimp only [z, t, k, a]
    rw [← haffine]
    exact hrate
  have hexpRate : Real.exp (-thetaCuspFirstLiouvilleRate x) ≤
      Real.exp (-z) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hP := exp_neg_le_thetaCuspFirstRateLowerEndpointCertificate64 (j := j) (by omega)
  have hT := exp_neg_le_expNegTruncPoly_nine ht
  have hP0 : 0 ≤ thetaCuspFirstRateLowerEndpointCertificate64 j :=
    (Real.exp_pos _).le.trans hP
  have hT0 : 0 ≤ (expNegTruncPoly 9).eval t := (Real.exp_pos _).le.trans hT
  rw [thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x) ≤
        Real.exp (-Real.pi) * (Real.exp (-z) * Real.exp (-t)) := by
      exact mul_le_mul_of_nonneg_left hexpRate (Real.exp_pos _).le
    _ ≤ (0.0432139182638 : ℝ) * (Real.exp (-z) * Real.exp (-t)) := by
      exact mul_le_mul_of_nonneg_right exp_neg_pi_rationalEnclosure_upper
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ ≤ (0.0432139182638 : ℝ) *
          (thetaCuspFirstRateLowerEndpointCertificate64 j *
            (expNegTruncPoly 9).eval t) := by
      gcongr
    _ = (0.0432139182638 : ℝ) * thetaCuspFirstRateLowerEndpointCertificate64 j *
        (expNegTruncPoly 9).eval
          (thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64)) := by
      dsimp only [t, k, a]
      ring

def thetaCuspFirstAtomRawLowerCertificate64 (r j : ℕ) (x : ℝ) : ℝ :=
  (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
    ((6.28318530717958647692 : ℝ) *
        thetaCuspSixtyFourthExpLowerTangent j x - 3) *
      ((0.0432139182637 : ℝ) *
        thetaCuspFirstRateUpperEndpointCertificate64 j *
          thetaCuspExpTaylorFive
            (thetaCuspFirstRateUpperSlope64 j *
              (((j + 1 : ℕ) : ℝ) / 64 - x)))

def thetaCuspFirstAtomRawUpperCertificate64 (r j : ℕ) (x : ℝ) : ℝ :=
  (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
    ((6.28318530717958647694 : ℝ) *
        thetaCuspSixtyFourthExpUpperChord j x - 3) *
      ((0.0432139182638 : ℝ) *
        thetaCuspFirstRateLowerEndpointCertificate64 j *
          (expNegTruncPoly 9).eval
            (thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64)))

theorem thetaCuspFirstAtomRawLowerCertificate64_le_density
    {r j : ℕ} (hj : j < 56) {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 64)) :
    thetaCuspFirstAtomRawLowerCertificate64 r j x ≤
      2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
  have htan := thetaCuspSixtyFourthExpLowerTangent_le_exp_two_mul hx.1
  have htan0 : 0 ≤ thetaCuspSixtyFourthExpLowerTangent j x := by
    rw [thetaCuspSixtyFourthExpLowerTangent]
    have hshift : 0 ≤ 1 + 2 * (x - (j : ℝ) / 64) := by linarith [hx.1]
    exact mul_nonneg
      (pow_nonneg (by norm_num [thetaCuspThirtySecondExpLower]) j) hshift
  have hinner :
      (6.28318530717958647692 : ℝ) *
          thetaCuspSixtyFourthExpLowerTangent j x - 3 ≤
        2 * Real.pi * Real.exp (2 * x) - 3 := by
    have hpi : (6.28318530717958647692 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_d20]
    calc
      (6.28318530717958647692 : ℝ) *
            thetaCuspSixtyFourthExpLowerTangent j x - 3 ≤
          (6.28318530717958647692 : ℝ) * Real.exp (2 * x) - 3 := by
        gcongr
      _ ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
        gcongr
  have hinner0 : 0 ≤
      (6.28318530717958647692 : ℝ) *
          thetaCuspSixtyFourthExpLowerTangent j x - 3 := by
    have hpow : 1 ≤ thetaCuspThirtySecondExpLower ^ j :=
      one_le_pow₀ (by norm_num [thetaCuspThirtySecondExpLower])
    rw [thetaCuspSixtyFourthExpLowerTangent]
    norm_num [thetaCuspThirtySecondExpLower] at *
    nlinarith
  have hg := thetaCuspFirstGibbsLower64_le hj hx
  have hP0 := thetaCuspFirstRateUpperEndpointCertificate64_pos hj
  have hT0 := thetaCuspExpTaylorFive_nonneg
    (mul_nonneg (thetaCuspFirstRateUpperSlope64_pos j).le
      (sub_nonneg.mpr hx.2))
  have hcertG0 : 0 ≤
      (0.0432139182637 : ℝ) * thetaCuspFirstRateUpperEndpointCertificate64 j *
        thetaCuspExpTaylorFive
          (thetaCuspFirstRateUpperSlope64 j *
            (((j + 1 : ℕ) : ℝ) / 64 - x)) := by positivity
  have hg0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hactualInner0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 :=
    hinner0.trans hinner
  have houter : (12.5663706143591729538 : ℝ) ≤ 4 * Real.pi := by
    nlinarith [Real.pi_gt_d20]
  rw [thetaCuspFirstAtomRawLowerCertificate64,
    thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          ((6.28318530717958647692 : ℝ) *
            thetaCuspSixtyFourthExpLowerTangent j x - 3) *
          ((0.0432139182637 : ℝ) *
            thetaCuspFirstRateUpperEndpointCertificate64 j *
              thetaCuspExpTaylorFive
                (thetaCuspFirstRateUpperSlope64 j *
                  (((j + 1 : ℕ) : ℝ) / 64 - x))) ≤
        (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          ((6.28318530717958647692 : ℝ) *
            thetaCuspSixtyFourthExpLowerTangent j x - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hinner0)
    _ ≤ (12.5663706143591729538 : ℝ) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hg0
    _ ≤ (4 * Real.pi) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualInner0) hg0
    _ = 2 * (x ^ (2 * r) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) := by ring

theorem thetaCuspFirstAtomRawDensity_le_upperCertificate64
    {r j : ℕ} (hj : j < 56) {x : ℝ}
    (hx : (j : ℝ) / 64 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 64)) :
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
      thetaCuspFirstAtomRawUpperCertificate64 r j x := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
  have hchord := exp_two_mul_le_thetaCuspSixtyFourthExpUpperChord hx
  have hinner : 2 * Real.pi * Real.exp (2 * x) - 3 ≤
      (6.28318530717958647694 : ℝ) *
        thetaCuspSixtyFourthExpUpperChord j x - 3 := by
    have hpi : 2 * Real.pi ≤ (6.28318530717958647694 : ℝ) := by
      nlinarith [Real.pi_lt_d20]
    calc
      2 * Real.pi * Real.exp (2 * x) - 3 ≤
          2 * Real.pi * thetaCuspSixtyFourthExpUpperChord j x - 3 := by
        gcongr
      _ ≤ (6.28318530717958647694 : ℝ) *
            thetaCuspSixtyFourthExpUpperChord j x - 3 := by
        have hchord0 : 0 ≤ thetaCuspSixtyFourthExpUpperChord j x :=
          (Real.exp_pos _).le.trans hchord
        gcongr
  have hactualInner0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_gt_d4]
  have hupperInner0 : 0 ≤
      (6.28318530717958647694 : ℝ) *
        thetaCuspSixtyFourthExpUpperChord j x - 3 := hactualInner0.trans hinner
  have hg := thetaCuspFirstGibbs_le_upper64 hj hx
  have hg0 : 0 ≤ thetaCuspLiouvilleGibbsAtom 1 x := by
    rw [thetaCuspLiouvilleGibbsAtom_apply]
    positivity
  have hcertG0 : 0 ≤
      (0.0432139182638 : ℝ) * thetaCuspFirstRateLowerEndpointCertificate64 j *
        (expNegTruncPoly 9).eval
          (thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64)) :=
    hg0.trans hg
  have houter : 4 * Real.pi ≤ (12.5663706143591729539 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  rw [thetaCuspFirstAtomRawUpperCertificate64,
    thetaCuspSourceTerm_one_eq_liouvilleGibbs]
  calc
    2 * (x ^ (2 * r) *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x)) =
        (4 * Real.pi) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x := by ring
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter (pow_nonneg hx0 _)) hactualInner0) hg0
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          ((6.28318530717958647694 : ℝ) *
            thetaCuspSixtyFourthExpUpperChord j x - 3) *
            thetaCuspLiouvilleGibbsAtom 1 x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by norm_num) (pow_nonneg hx0 _))) hg0
    _ ≤ (12.5663706143591729539 : ℝ) * x ^ (2 * r) *
          ((6.28318530717958647694 : ℝ) *
            thetaCuspSixtyFourthExpUpperChord j x - 3) *
          ((0.0432139182638 : ℝ) *
            thetaCuspFirstRateLowerEndpointCertificate64 j *
              (expNegTruncPoly 9).eval
                (thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64))) := by
      exact mul_le_mul_of_nonneg_left hg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 _)) hupperInner0)

/-- Exact rational integral of `x^r (x-a)^m` over `[a,b]`. -/
def thetaCuspIntervalPowAddMass (r m : ℕ) (a b : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ (q + m) * a ^ (m - q) * (m.choose q : ℝ) *
      ((b ^ (r + q + 1) - a ^ (r + q + 1)) / (r + q + 1 : ℕ))

theorem intervalIntegral_pow_mul_add_pow_eq_thetaCuspIntervalPowAddMass
    (r m : ℕ) (a b : ℝ) :
    (∫ x in a..b, x ^ r * (x - a) ^ m) =
      thetaCuspIntervalPowAddMass r m a b := by
  rw [show (fun x : ℝ => x ^ r * (x - a) ^ m) = fun x : ℝ =>
      ∑ q ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ (q + m) * a ^ (m - q) * (m.choose q : ℝ)) *
          x ^ (r + q) by
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

def thetaCuspFirstSourceLowerAffineConstant64 (j : ℕ) : ℝ :=
  (6.28318530717958647692 : ℝ) * thetaCuspThirtySecondExpLower ^ j *
      (1 - 2 * ((j : ℝ) / 64)) - 3

def thetaCuspFirstSourceLowerAffineSlope64 (j : ℕ) : ℝ :=
  2 * (6.28318530717958647692 : ℝ) * thetaCuspThirtySecondExpLower ^ j

def thetaCuspFirstSourceUpperAffineConstant64 (j : ℕ) : ℝ :=
  (6.28318530717958647694 : ℝ) * thetaCuspThirtySecondExpUpper ^ j - 3

def thetaCuspFirstSourceUpperAffineSlope64 (j : ℕ) : ℝ :=
  64 * (6.28318530717958647694 : ℝ) *
    (thetaCuspThirtySecondExpUpper ^ (j + 1) -
      thetaCuspThirtySecondExpUpper ^ j)

theorem thetaCuspFirstSourceLowerFactor64_eq_affine (j : ℕ) (x : ℝ) :
    (6.28318530717958647692 : ℝ) *
        thetaCuspSixtyFourthExpLowerTangent j x - 3 =
      thetaCuspFirstSourceLowerAffineConstant64 j +
        thetaCuspFirstSourceLowerAffineSlope64 j * x := by
  rw [thetaCuspSixtyFourthExpLowerTangent,
    thetaCuspFirstSourceLowerAffineConstant64,
    thetaCuspFirstSourceLowerAffineSlope64]
  ring

theorem thetaCuspFirstSourceUpperFactor64_eq_affine (j : ℕ) (x : ℝ) :
    (6.28318530717958647694 : ℝ) *
        thetaCuspSixtyFourthExpUpperChord j x - 3 =
      thetaCuspFirstSourceUpperAffineConstant64 j +
        thetaCuspFirstSourceUpperAffineSlope64 j * (x - (j : ℝ) / 64) := by
  rw [thetaCuspSixtyFourthExpUpperChord,
    thetaCuspFirstSourceUpperAffineConstant64,
    thetaCuspFirstSourceUpperAffineSlope64]
  ring

/-- Exact algebraic mass for a polynomial times a backward fifth-order Taylor section. -/
def thetaCuspPowAffineSubTaylorMass
    (r : ℕ) (A B a b k : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 6,
    (k ^ m / (m.factorial : ℝ)) *
      (A * thetaCuspIntervalPowSubMass r m a b +
        B * thetaCuspIntervalPowSubMass (r + 1) m a b)

theorem intervalIntegral_pow_affine_mul_subTaylor_eq_mass
    (r : ℕ) (A B a b k : ℝ) :
    (∫ x in a..b,
      x ^ r * (A + B * x) * thetaCuspExpTaylorFive (k * (b - x))) =
      thetaCuspPowAffineSubTaylorMass r A B a b k := by
  rw [show (fun x : ℝ =>
      x ^ r * (A + B * x) * thetaCuspExpTaylorFive (k * (b - x))) =
    fun x : ℝ => ∑ m ∈ Finset.range 6,
      (k ^ m / (m.factorial : ℝ)) *
        (A * (x ^ r * (b - x) ^ m) +
          B * (x ^ (r + 1) * (b - x) ^ m)) by
    funext x
    rw [thetaCuspExpTaylorFive_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_pow, pow_succ]
    ring]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass,
        intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass]
    · exact (by fun_prop : Continuous (fun x : ℝ =>
          A * (x ^ r * (b - x) ^ m))).intervalIntegrable a b
    · exact (by fun_prop : Continuous (fun x : ℝ =>
          B * (x ^ (r + 1) * (b - x) ^ m))).intervalIntegrable a b
  · intro m hm
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (k ^ m / (m.factorial : ℝ)) *
        (A * (x ^ r * (b - x) ^ m) +
          B * (x ^ (r + 1) * (b - x) ^ m)))).intervalIntegrable a b

def thetaCuspFirstAtomRawLowerIntervalMass64 (r j : ℕ) : ℝ :=
  (12.5663706143591729538 : ℝ) * (0.0432139182637 : ℝ) *
    thetaCuspFirstRateUpperEndpointCertificate64 j *
      thetaCuspPowAffineSubTaylorMass (2 * r)
        (thetaCuspFirstSourceLowerAffineConstant64 j)
        (thetaCuspFirstSourceLowerAffineSlope64 j)
        ((j : ℝ) / 64) (((j + 1 : ℕ) : ℝ) / 64)
        (thetaCuspFirstRateUpperSlope64 j)

theorem intervalIntegral_thetaCuspFirstAtomRawLowerCertificate64_eq_mass
    (r j : ℕ) :
    (∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64),
      thetaCuspFirstAtomRawLowerCertificate64 r j x) =
      thetaCuspFirstAtomRawLowerIntervalMass64 r j := by
  rw [show (fun x : ℝ => thetaCuspFirstAtomRawLowerCertificate64 r j x) =
      fun x : ℝ =>
        ((12.5663706143591729538 : ℝ) * (0.0432139182637 : ℝ) *
          thetaCuspFirstRateUpperEndpointCertificate64 j) *
        (x ^ (2 * r) *
          (thetaCuspFirstSourceLowerAffineConstant64 j +
            thetaCuspFirstSourceLowerAffineSlope64 j * x) *
          thetaCuspExpTaylorFive
            (thetaCuspFirstRateUpperSlope64 j *
              ((((j + 1 : ℕ) : ℝ) / 64) - x))) by
    funext x
    rw [thetaCuspFirstAtomRawLowerCertificate64,
      thetaCuspFirstSourceLowerFactor64_eq_affine]
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_pow_affine_mul_subTaylor_eq_mass,
    thetaCuspFirstAtomRawLowerIntervalMass64]

/-- Exact algebraic mass for a polynomial times a forward alternating exponential section. -/
def thetaCuspPowAffineAddExpNegMass
    (r : ℕ) (A B a b k : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 9,
    (((-1 : ℝ) ^ m * k ^ m) / (m.factorial : ℝ)) *
      (A * thetaCuspIntervalPowAddMass r m a b +
        B * thetaCuspIntervalPowAddMass r (m + 1) a b)

theorem intervalIntegral_pow_affine_mul_addExpNeg_eq_mass
    (r : ℕ) (A B a b k : ℝ) :
    (∫ x in a..b,
      x ^ r * (A + B * (x - a)) *
        (expNegTruncPoly 9).eval (k * (x - a))) =
      thetaCuspPowAffineAddExpNegMass r A B a b k := by
  rw [show (fun x : ℝ =>
      x ^ r * (A + B * (x - a)) *
        (expNegTruncPoly 9).eval (k * (x - a))) =
    fun x : ℝ => ∑ m ∈ Finset.range 9,
      (((-1 : ℝ) ^ m * k ^ m) / (m.factorial : ℝ)) *
        (A * (x ^ r * (x - a) ^ m) +
          B * (x ^ r * (x - a) ^ (m + 1))) by
    funext x
    rw [eval_expNegTruncPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_pow, pow_succ]
    ring]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral_pow_mul_add_pow_eq_thetaCuspIntervalPowAddMass,
        intervalIntegral_pow_mul_add_pow_eq_thetaCuspIntervalPowAddMass]
    · exact (by fun_prop : Continuous (fun x : ℝ =>
          A * (x ^ r * (x - a) ^ m))).intervalIntegrable a b
    · exact (by fun_prop : Continuous (fun x : ℝ =>
          B * (x ^ r * (x - a) ^ (m + 1)))).intervalIntegrable a b
  · intro m hm
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (((-1 : ℝ) ^ m * k ^ m) / (m.factorial : ℝ)) *
        (A * (x ^ r * (x - a) ^ m) +
          B * (x ^ r * (x - a) ^ (m + 1))))).intervalIntegrable a b

def thetaCuspFirstAtomRawUpperIntervalMass64 (r j : ℕ) : ℝ :=
  (12.5663706143591729539 : ℝ) * (0.0432139182638 : ℝ) *
    thetaCuspFirstRateLowerEndpointCertificate64 j *
      thetaCuspPowAffineAddExpNegMass (2 * r)
        (thetaCuspFirstSourceUpperAffineConstant64 j)
        (thetaCuspFirstSourceUpperAffineSlope64 j)
        ((j : ℝ) / 64) (((j + 1 : ℕ) : ℝ) / 64)
        (thetaCuspFirstRateLowerSlope64 j)

theorem intervalIntegral_thetaCuspFirstAtomRawUpperCertificate64_eq_mass
    (r j : ℕ) :
    (∫ x in (j : ℝ) / 64..(((j + 1 : ℕ) : ℝ) / 64),
      thetaCuspFirstAtomRawUpperCertificate64 r j x) =
      thetaCuspFirstAtomRawUpperIntervalMass64 r j := by
  rw [show (fun x : ℝ => thetaCuspFirstAtomRawUpperCertificate64 r j x) =
      fun x : ℝ =>
        ((12.5663706143591729539 : ℝ) * (0.0432139182638 : ℝ) *
          thetaCuspFirstRateLowerEndpointCertificate64 j) *
        (x ^ (2 * r) *
          (thetaCuspFirstSourceUpperAffineConstant64 j +
            thetaCuspFirstSourceUpperAffineSlope64 j * (x - (j : ℝ) / 64)) *
          (expNegTruncPoly 9).eval
            (thetaCuspFirstRateLowerSlope64 j * (x - (j : ℝ) / 64))) by
    funext x
    rw [thetaCuspFirstAtomRawUpperCertificate64,
      thetaCuspFirstSourceUpperFactor64_eq_affine]
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_pow_affine_mul_addExpNeg_eq_mass,
    thetaCuspFirstAtomRawUpperIntervalMass64]

end

end RHTower
