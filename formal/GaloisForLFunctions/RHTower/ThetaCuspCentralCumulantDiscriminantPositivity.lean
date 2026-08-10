import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniCentralCumulantGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentFloor
import GaloisForLFunctions.RHTower.PrimeArchThetaReflectedBudgetTailTransfer
import GaloisForLFunctions.RHTower.ThetaSingleGibbsLikelihoodSingleLossClosure
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# Unconditional positivity of the central Route-U cumulant discriminant

The central Route-U Euler-contact germ is the normalized cubic

`3 m₀ m₁ m₃ + 15 m₁² m₂ - 10 m₀ m₂²`

of the completed theta-source moments.  Its true margin is small in raw coordinates, so this file
certifies the four dominant first-atom moments by rational analytic envelopes on eighty intervals.
The lower envelope uses a convex exponential chord and positive Taylor sections.  The upper
envelope uses the matching tangent and an even alternating Taylor section.  A separate symbolic
super-exponential cusp estimate controls the omitted ray.  The exact reflected half-density budget
and likelihood order then transfer only the two upper endpoints needed by the negative cubic term.

No floating-point integration, zero table, added axiom, or RH assumption occurs in the proof.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-! ## Rational exponential clock -/

def thetaCuspRouteUExpStepLower : ℝ := 1.0253151205244

def thetaCuspRouteUExpStepUpper : ℝ := 1.0253151205245

theorem thetaCuspRouteUExpStepLower_le_exp :
    thetaCuspRouteUExpStepLower ≤ Real.exp (1 / 40 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 40) 8
  norm_num [thetaCuspRouteUExpStepLower, Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem thetaCuspRouteU_exp_le_ExpStepUpper :
    Real.exp (1 / 40 : ℝ) ≤ thetaCuspRouteUExpStepUpper := by
  have h := Real.exp_bound (x := (1 / 40 : ℝ)) (by norm_num) (n := 12) (by norm_num)
  norm_num [thetaCuspRouteUExpStepUpper, Finset.sum_range_succ, Nat.factorial] at h ⊢
  have hu := (abs_le.mp h).2
  linarith

theorem thetaCuspRouteU_exp_nat_step_lower (j : ℕ) :
    thetaCuspRouteUExpStepLower ^ j ≤ Real.exp ((j : ℝ) / 40) := by
  rw [show (j : ℝ) / 40 = (j : ℕ) * (1 / 40 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀
    (by norm_num [thetaCuspRouteUExpStepLower])
    thetaCuspRouteUExpStepLower_le_exp j

theorem thetaCuspRouteU_exp_nat_step_upper (j : ℕ) :
    Real.exp ((j : ℝ) / 40) ≤ thetaCuspRouteUExpStepUpper ^ j := by
  rw [show (j : ℝ) / 40 = (j : ℕ) * (1 / 40 : ℝ) by ring,
    Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le thetaCuspRouteU_exp_le_ExpStepUpper j

def thetaCuspRouteUExpChord (j : ℕ) (x : ℝ) : ℝ :=
  let t : ℝ := 80 * x - j
  (1 - t) * thetaCuspRouteUExpStepUpper ^ j +
    t * thetaCuspRouteUExpStepUpper ^ (j + 1)

theorem exp_two_mul_le_thetaCuspRouteUExpChord
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 80)) :
    Real.exp (2 * x) ≤ thetaCuspRouteUExpChord j x := by
  let t : ℝ := 80 * x - j
  have ht0 : 0 ≤ t := by dsimp only [t]; push_cast at hx ⊢; linarith
  have ht1 : t ≤ 1 := by dsimp only [t]; push_cast at hx ⊢; linarith
  have hconv := convexOn_exp.2
    (Set.mem_univ ((j : ℝ) / 40))
    (Set.mem_univ (((j + 1 : ℕ) : ℝ) / 40))
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  have harg :
      (1 - t) * ((j : ℝ) / 40) +
          t * (((j + 1 : ℕ) : ℝ) / 40) = 2 * x := by
    dsimp only [t]
    push_cast
    ring
  simp only [smul_eq_mul] at hconv
  rw [harg] at hconv
  have hj := thetaCuspRouteU_exp_nat_step_upper j
  have hj1 := thetaCuspRouteU_exp_nat_step_upper (j + 1)
  calc
    Real.exp (2 * x) ≤
        (1 - t) * Real.exp ((j : ℝ) / 40) +
          t * Real.exp (((j + 1 : ℕ) : ℝ) / 40) := hconv
    _ ≤ (1 - t) * thetaCuspRouteUExpStepUpper ^ j +
          t * thetaCuspRouteUExpStepUpper ^ (j + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hj1 ht0)
    _ = thetaCuspRouteUExpChord j x := by
      simp only [thetaCuspRouteUExpChord, t]

/-! ## Lower interval envelope -/

def thetaCuspRouteULowerRate (j : ℕ) (x : ℝ) : ℝ :=
  (3.141593 : ℝ) * (thetaCuspRouteUExpChord j x - 1) - 5 * x / 2

def thetaCuspRouteULowerRateSlope (j : ℕ) : ℝ :=
  (3.141593 : ℝ) * 80 *
      (thetaCuspRouteUExpStepUpper ^ (j + 1) -
        thetaCuspRouteUExpStepUpper ^ j) - 5 / 2

def thetaCuspRouteULowerEndpoint (j : ℕ) : ℝ :=
  (expNegTruncPoly 64).eval
    (thetaCuspRouteULowerRate j (((j + 1 : ℕ) : ℝ) / 80))

def thetaCuspRouteUExpTaylorTwelve (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 13, u ^ n / (n.factorial : ℝ)

def thetaCuspRouteULowerCertificate (r j : ℕ) (x : ℝ) : ℝ :=
  (0.543 : ℝ) * thetaCuspRouteULowerEndpoint j * x ^ r *
    ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
    thetaCuspRouteUExpTaylorTwelve
      (thetaCuspRouteULowerRateSlope j * (((j + 1 : ℕ) : ℝ) / 80 - x))

theorem thetaCuspRouteUExpTaylorTwelve_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaCuspRouteUExpTaylorTwelve u := by
  rw [thetaCuspRouteUExpTaylorTwelve]
  exact Finset.sum_nonneg fun n _ => by positivity

theorem thetaCuspRouteUExpTaylorTwelve_le_exp {u : ℝ} (hu : 0 ≤ u) :
    thetaCuspRouteUExpTaylorTwelve u ≤ Real.exp u := by
  simpa only [thetaCuspRouteUExpTaylorTwelve] using Real.sum_le_exp_of_nonneg hu 13

theorem thetaCuspFirstLiouvilleRate_le_routeULowerRate
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 80)) :
    thetaCuspFirstLiouvilleRate x ≤ thetaCuspRouteULowerRate j x := by
  have hx0 : 0 ≤ x := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 80 := by positivity
    linarith [hx.1]
  have hchord := exp_two_mul_le_thetaCuspRouteUExpChord hx
  have hone : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
  have hchord0 : 0 ≤ thetaCuspRouteUExpChord j x - 1 := by linarith
  have hpi : Real.pi < (3.141593 : ℝ) := by nlinarith [Real.pi_lt_d20]
  rw [thetaCuspFirstLiouvilleRate, thetaCuspRouteULowerRate]
  calc
    Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2 ≤
        Real.pi * (thetaCuspRouteUExpChord j x - 1) - 5 * x / 2 := by gcongr
    _ ≤ (3.141593 : ℝ) * (thetaCuspRouteUExpChord j x - 1) - 5 * x / 2 := by
      gcongr

theorem thetaCuspRouteULowerRate_affine (j : ℕ) (x : ℝ) :
    thetaCuspRouteULowerRate j x =
      thetaCuspRouteULowerRate j (((j + 1 : ℕ) : ℝ) / 80) -
        thetaCuspRouteULowerRateSlope j * (((j + 1 : ℕ) : ℝ) / 80 - x) := by
  simp only [thetaCuspRouteULowerRate, thetaCuspRouteULowerRateSlope,
    thetaCuspRouteUExpChord, thetaCuspRouteUExpStepUpper]
  push_cast
  ring

theorem thetaCuspRouteULowerRateSlope_pos
    {j : ℕ} (hj : j < 80) : 0 < thetaCuspRouteULowerRateSlope j := by
  have hq : (1 : ℝ) ≤ thetaCuspRouteUExpStepUpper ^ j := by
    exact one_le_pow₀ (by norm_num [thetaCuspRouteUExpStepUpper])
  rw [thetaCuspRouteULowerRateSlope]
  have hfactor :
      thetaCuspRouteUExpStepUpper ^ (j + 1) - thetaCuspRouteUExpStepUpper ^ j =
        thetaCuspRouteUExpStepUpper ^ j *
          (thetaCuspRouteUExpStepUpper - 1) := by
    rw [pow_succ]
    ring
  rw [hfactor]
  norm_num [thetaCuspRouteUExpStepUpper] at hq ⊢
  nlinarith

theorem thetaCuspRouteULowerRate_endpoint_pos
    {j : ℕ} (hj : j < 80) :
    0 < thetaCuspRouteULowerRate j (((j + 1 : ℕ) : ℝ) / 80) := by
  interval_cases j <;>
    norm_num [thetaCuspRouteULowerRate, thetaCuspRouteUExpChord,
      thetaCuspRouteUExpStepUpper]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
theorem thetaCuspRouteULowerEndpoint_pos
    {j : ℕ} (hj : j < 80) : 0 < thetaCuspRouteULowerEndpoint j := by
  interval_cases j <;>
    norm_num [thetaCuspRouteULowerEndpoint, thetaCuspRouteULowerRate,
      thetaCuspRouteUExpChord, thetaCuspRouteUExpStepUpper,
      eval_expNegTruncPoly, Finset.sum_range_succ, Nat.factorial]

theorem thetaCuspRouteULowerEndpoint_lt_exp
    {j : ℕ} (hj : j < 80) :
    thetaCuspRouteULowerEndpoint j ≤
      Real.exp (-thetaCuspRouteULowerRate j (((j + 1 : ℕ) : ℝ) / 80)) := by
  have hz := thetaCuspRouteULowerRate_endpoint_pos hj
  have h := expNegTruncPoly_sub_exp_oriented_pos (m := 64) (by norm_num) hz
  norm_num at h
  rw [thetaCuspRouteULowerEndpoint]
  simpa only [Nat.cast_add, Nat.cast_one] using h.le

theorem thetaCuspRouteU_outer_lower :
    (0.543 : ℝ) ≤ 4 * Real.pi * Real.exp (-Real.pi) := by
  have hp : (3.14159265358979323846 : ℝ) ≤ Real.pi := Real.pi_gt_d20.le
  have he := exp_neg_pi_rationalEnclosure_lower
  have hmul := mul_le_mul hp he (by norm_num) (by positivity : 0 ≤ Real.pi)
  nlinarith

theorem thetaCuspRouteULowerCertificate_le_density
    {r j : ℕ} (hj : j < 80) {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 80)) :
    thetaCuspRouteULowerCertificate r j x ≤
      2 * (x ^ r * thetaCuspSourceTerm x 1) := by
  have hx0 : 0 ≤ x := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 80 := by positivity
    linarith [hx.1]
  have hslope := thetaCuspRouteULowerRateSlope_pos hj
  have hgap : 0 ≤ (((j + 1 : ℕ) : ℝ) / 80 - x) := by
    push_cast at hx ⊢
    linarith
  have hu : 0 ≤ thetaCuspRouteULowerRateSlope j *
      (((j + 1 : ℕ) : ℝ) / 80 - x) := mul_nonneg hslope.le hgap
  have hrate := thetaCuspFirstLiouvilleRate_le_routeULowerRate hx
  have haffine := thetaCuspRouteULowerRate_affine j x
  have hendpoint := thetaCuspRouteULowerEndpoint_lt_exp hj
  have hprop := thetaCuspRouteUExpTaylorTwelve_le_exp hu
  have hendpoint0 := (thetaCuspRouteULowerEndpoint_pos hj).le
  have hprop0 := thetaCuspRouteUExpTaylorTwelve_nonneg hu
  have hdecay :
      thetaCuspRouteULowerEndpoint j *
          thetaCuspRouteUExpTaylorTwelve
            (thetaCuspRouteULowerRateSlope j *
              (((j + 1 : ℕ) : ℝ) / 80 - x)) ≤
        Real.exp (-thetaCuspFirstLiouvilleRate x) := by
    calc
      _ ≤ Real.exp (-thetaCuspRouteULowerRate j (((j + 1 : ℕ) : ℝ) / 80)) *
          Real.exp (thetaCuspRouteULowerRateSlope j *
            (((j + 1 : ℕ) : ℝ) / 80 - x)) :=
        mul_le_mul hendpoint hprop hprop0 (Real.exp_pos _).le
      _ = Real.exp (-thetaCuspRouteULowerRate j x) := by
        rw [← Real.exp_add, haffine]
        congr 1
        ring
      _ ≤ Real.exp (-thetaCuspFirstLiouvilleRate x) :=
        Real.exp_le_exp.mpr (neg_le_neg hrate)
  have hsourceTaylor := thetaCuspRouteUExpTaylorTwelve_le_exp (u := 2 * x) (by positivity)
  have hinner :
      (6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3 ≤
        2 * Real.pi * Real.exp (2 * x) - 3 := by
    have hp : (6.28318 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_d20]
    calc
      _ ≤ (6.28318 : ℝ) * Real.exp (2 * x) - 3 := by gcongr
      _ ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by gcongr
  have hinner0 :
      0 ≤ (6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3 := by
    have ht : 1 ≤ thetaCuspRouteUExpTaylorTwelve (2 * x) := by
      rw [thetaCuspRouteUExpTaylorTwelve]
      have hnon : ∀ n ∈ Finset.range 13,
          0 ≤ (2 * x) ^ n / (n.factorial : ℝ) := fun n _ => by positivity
      have hmem : 0 ∈ Finset.range 13 := by simp
      have hsingle := Finset.single_le_sum hnon hmem
      norm_num at hsingle ⊢
      exact hsingle
    nlinarith
  have hactualInner0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := hinner0.trans hinner
  have houter := thetaCuspRouteU_outer_lower
  rw [thetaCuspRouteULowerCertificate,
    thetaCuspSourceTerm_one_eq_liouvilleGibbs,
    thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    (0.543 : ℝ) * thetaCuspRouteULowerEndpoint j * x ^ r *
          ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
          thetaCuspRouteUExpTaylorTwelve
            (thetaCuspRouteULowerRateSlope j *
              (((j + 1 : ℕ) : ℝ) / 80 - x)) =
        (0.543 : ℝ) * x ^ r *
          ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
          (thetaCuspRouteULowerEndpoint j *
            thetaCuspRouteUExpTaylorTwelve
              (thetaCuspRouteULowerRateSlope j *
                (((j + 1 : ℕ) : ℝ) / 80 - x))) := by ring
    _ ≤ (0.543 : ℝ) * x ^ r *
          ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
          Real.exp (-thetaCuspFirstLiouvilleRate x) := by
      exact mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 r)) hinner0)
    _ ≤ (0.543 : ℝ) * x ^ r *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          Real.exp (-thetaCuspFirstLiouvilleRate x) := by
      gcongr
    _ ≤ (4 * Real.pi * Real.exp (-Real.pi)) * x ^ r *
          (2 * Real.pi * Real.exp (2 * x) - 3) *
          Real.exp (-thetaCuspFirstLiouvilleRate x) := by
      gcongr
    _ = 2 * (x ^ r *
          (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
            (Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x)))) := by ring

/-! ## Exact lower certificate integrals -/

def thetaCuspRouteULowerTaylorMass (r : ℕ) (a b k : ℝ) : ℝ :=
  (6.28318 : ℝ) *
      ∑ n ∈ Finset.range 13,
        ((2 : ℝ) ^ n / (n.factorial : ℝ)) *
          ∑ m ∈ Finset.range 13,
            (k ^ m / (m.factorial : ℝ)) *
              thetaCuspIntervalPowSubMass (r + n) m a b -
    3 * ∑ m ∈ Finset.range 13,
      (k ^ m / (m.factorial : ℝ)) * thetaCuspIntervalPowSubMass r m a b

theorem thetaCuspRouteUExpTaylorTwelve_eq_sum (u : ℝ) :
    thetaCuspRouteUExpTaylorTwelve u =
      ∑ n ∈ Finset.range 13, u ^ n / (n.factorial : ℝ) := rfl

theorem intervalIntegral_thetaCuspRouteULowerTaylorShape_eq_mass
    (r : ℕ) (a b k : ℝ) :
    (∫ x in a..b,
      x ^ r * ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
        thetaCuspRouteUExpTaylorTwelve (k * (b - x))) =
      thetaCuspRouteULowerTaylorMass r a b k := by
  have hfun :
      (fun x : ℝ =>
        x ^ r * ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
          thetaCuspRouteUExpTaylorTwelve (k * (b - x))) =
      fun x : ℝ =>
        (6.28318 : ℝ) *
            ∑ n ∈ Finset.range 13,
              ∑ m ∈ Finset.range 13,
                (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
                  (k ^ m / (m.factorial : ℝ))) *
                    (x ^ (r + n) * (b - x) ^ m) -
          3 * ∑ m ∈ Finset.range 13,
            (k ^ m / (m.factorial : ℝ)) * (x ^ r * (b - x) ^ m) := by
    funext x
    rw [thetaCuspRouteUExpTaylorTwelve_eq_sum (2 * x),
      thetaCuspRouteUExpTaylorTwelve_eq_sum (k * (b - x))]
    simp_rw [mul_pow, pow_add]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    congr 3 <;> ring
    funext y
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hfun]
  rw [intervalIntegral.integral_sub
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      (6.28318 : ℝ) *
        ∑ n ∈ Finset.range 13, ∑ m ∈ Finset.range 13,
          (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
            (k ^ m / (m.factorial : ℝ))) *
              (x ^ (r + n) * (b - x) ^ m))).intervalIntegrable a b)
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      3 * ∑ m ∈ Finset.range 13,
        (k ^ m / (m.factorial : ℝ)) *
          (x ^ r * (b - x) ^ m))).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply congrArg₂ (· - ·)
    · apply congrArg ((6.28318 : ℝ) * ·)
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum, intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass]
        ring
      · intro m hm
        exact (by fun_prop : Continuous (fun x : ℝ =>
          (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
            (k ^ m / (m.factorial : ℝ))) *
              (x ^ (r + n) * (b - x) ^ m))).intervalIntegrable a b
    · rw [intervalIntegral.integral_finsetSum]
      · apply congrArg (3 * ·)
        apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_pow_mul_sub_pow_eq_thetaCuspIntervalPowSubMass]
      · intro m hm
        exact (by fun_prop : Continuous (fun x : ℝ =>
          (k ^ m / (m.factorial : ℝ)) *
            (x ^ r * (b - x) ^ m))).intervalIntegrable a b
  · intro n hn
    exact (by fun_prop : Continuous (fun x : ℝ =>
      ∑ m ∈ Finset.range 13,
        (((2 : ℝ) ^ n / (n.factorial : ℝ)) *
          (k ^ m / (m.factorial : ℝ))) *
            (x ^ (r + n) * (b - x) ^ m))).intervalIntegrable a b

def thetaCuspRouteULowerIntervalMass (r j : ℕ) : ℝ :=
  (0.543 : ℝ) * thetaCuspRouteULowerEndpoint j *
    thetaCuspRouteULowerTaylorMass r
      ((j : ℝ) / 80) (((j + 1 : ℕ) : ℝ) / 80)
      (thetaCuspRouteULowerRateSlope j)

theorem intervalIntegral_thetaCuspRouteULowerCertificate_eq_mass
    (r j : ℕ) :
    (∫ x in (j : ℝ) / 80..(((j + 1 : ℕ) : ℝ) / 80),
      thetaCuspRouteULowerCertificate r j x) =
      thetaCuspRouteULowerIntervalMass r j := by
  rw [show (fun x : ℝ => thetaCuspRouteULowerCertificate r j x) =
      fun x : ℝ =>
        ((0.543 : ℝ) * thetaCuspRouteULowerEndpoint j) *
          (x ^ r *
            ((6.28318 : ℝ) * thetaCuspRouteUExpTaylorTwelve (2 * x) - 3) *
            thetaCuspRouteUExpTaylorTwelve
              (thetaCuspRouteULowerRateSlope j *
                ((((j + 1 : ℕ) : ℝ) / 80) - x))) by
    funext x
    rw [thetaCuspRouteULowerCertificate]
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_thetaCuspRouteULowerTaylorShape_eq_mass,
    thetaCuspRouteULowerIntervalMass]

end

end RHTower
