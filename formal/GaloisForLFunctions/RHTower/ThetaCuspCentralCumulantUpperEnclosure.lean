import GaloisForLFunctions.RHTower.ThetaCuspCentralCumulantDiscriminantPositivity

/-!
# Upper rational envelope for the dominant theta atom

This is the tangent companion to the lower chord certificate.  On each of the same eighty
intervals, a rational exponential tangent minorizes the Liouville rate.  Odd-length alternating
Taylor sections (even top degree) majorize the two remaining decays.  The resulting certificate is
a polynomial with an exact rational integral.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators Interval

namespace RHTower

noncomputable section

def thetaCuspRouteUUpperRate (j : ℕ) (x : ℝ) : ℝ :=
  (3.141592 : ℝ) *
      (thetaCuspRouteUExpStepLower ^ j *
          (1 + 2 * (x - (j : ℝ) / 80)) - 1) -
    5 * x / 2

def thetaCuspRouteUUpperRateSlope (j : ℕ) : ℝ :=
  2 * (3.141592 : ℝ) * thetaCuspRouteUExpStepLower ^ j - 5 / 2

def thetaCuspRouteUUpperEndpoint (j : ℕ) : ℝ :=
  (expNegTruncPoly 65).eval
    (thetaCuspRouteUUpperRate j ((j : ℝ) / 80))

def thetaCuspRouteUExpNegTaylorEight (u : ℝ) : ℝ :=
  (expNegTruncPoly 9).eval u

def thetaCuspRouteUUpperChordSlope (j : ℕ) : ℝ :=
  80 * (thetaCuspRouteUExpStepUpper ^ (j + 1) -
    thetaCuspRouteUExpStepUpper ^ j)

def thetaCuspRouteUUpperChordIntercept (j : ℕ) : ℝ :=
  thetaCuspRouteUExpStepUpper ^ j -
    (j : ℝ) * (thetaCuspRouteUExpStepUpper ^ (j + 1) -
      thetaCuspRouteUExpStepUpper ^ j)

def thetaCuspRouteUUpperInnerSlope (j : ℕ) : ℝ :=
  (6.283186 : ℝ) * thetaCuspRouteUUpperChordSlope j

def thetaCuspRouteUUpperInnerIntercept (j : ℕ) : ℝ :=
  (6.283186 : ℝ) * thetaCuspRouteUUpperChordIntercept j - 3

def thetaCuspRouteUUpperCertificate (r j : ℕ) (x : ℝ) : ℝ :=
  (0.543043 : ℝ) * thetaCuspRouteUUpperEndpoint j * x ^ r *
    (thetaCuspRouteUUpperInnerIntercept j +
      thetaCuspRouteUUpperInnerSlope j * x) *
    thetaCuspRouteUExpNegTaylorEight
      (thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80))

theorem thetaCuspRouteUExpChord_eq_affine (j : ℕ) (x : ℝ) :
    thetaCuspRouteUExpChord j x =
      thetaCuspRouteUUpperChordIntercept j +
        thetaCuspRouteUUpperChordSlope j * x := by
  simp only [thetaCuspRouteUExpChord, thetaCuspRouteUUpperChordIntercept,
    thetaCuspRouteUUpperChordSlope]
  push_cast
  ring

theorem thetaCuspRouteUUpperInner_eq_chord (j : ℕ) (x : ℝ) :
    thetaCuspRouteUUpperInnerIntercept j + thetaCuspRouteUUpperInnerSlope j * x =
      (6.283186 : ℝ) * thetaCuspRouteUExpChord j x - 3 := by
  rw [thetaCuspRouteUExpChord_eq_affine]
  simp only [thetaCuspRouteUUpperInnerIntercept, thetaCuspRouteUUpperInnerSlope]
  ring

theorem thetaCuspRouteU_tangent_le_exp_two_mul
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x) :
    thetaCuspRouteUExpStepLower ^ j *
        (1 + 2 * (x - (j : ℝ) / 80)) ≤ Real.exp (2 * x) := by
  have hu : 0 ≤ 2 * (x - (j : ℝ) / 80) := by linarith
  have hstep := thetaCuspRouteU_exp_nat_step_lower j
  have hlin : 1 + 2 * (x - (j : ℝ) / 80) ≤
      Real.exp (2 * (x - (j : ℝ) / 80)) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * (x - (j : ℝ) / 80))
  have hlin0 : 0 ≤ 1 + 2 * (x - (j : ℝ) / 80) := by linarith
  calc
    _ ≤ Real.exp ((j : ℝ) / 40) *
        (1 + 2 * (x - (j : ℝ) / 80)) :=
      mul_le_mul_of_nonneg_right hstep hlin0
    _ ≤ Real.exp ((j : ℝ) / 40) *
        Real.exp (2 * (x - (j : ℝ) / 80)) :=
      mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    _ = Real.exp (2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem thetaCuspRouteUUpperRate_le_firstLiouvilleRate
    {j : ℕ} {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x) :
    thetaCuspRouteUUpperRate j x ≤ thetaCuspFirstLiouvilleRate x := by
  have htangent := thetaCuspRouteU_tangent_le_exp_two_mul hx
  have htan1 : 1 ≤ thetaCuspRouteUExpStepLower ^ j *
      (1 + 2 * (x - (j : ℝ) / 80)) := by
    have hpow : 1 ≤ thetaCuspRouteUExpStepLower ^ j :=
      one_le_pow₀ (by norm_num [thetaCuspRouteUExpStepLower])
    have hlin : 1 ≤ 1 + 2 * (x - (j : ℝ) / 80) := by linarith
    simpa only [one_mul] using
      mul_le_mul hpow hlin (by norm_num) (zero_le_one.trans hpow)
  have hpi : (3.141592 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_d20]
  rw [thetaCuspRouteUUpperRate, thetaCuspFirstLiouvilleRate]
  calc
    _ ≤ Real.pi *
        (thetaCuspRouteUExpStepLower ^ j *
          (1 + 2 * (x - (j : ℝ) / 80)) - 1) - 5 * x / 2 := by gcongr
    _ ≤ Real.pi * (Real.exp (2 * x) - 1) - 5 * x / 2 := by gcongr

theorem thetaCuspRouteUUpperRate_affine (j : ℕ) (x : ℝ) :
    thetaCuspRouteUUpperRate j x =
      thetaCuspRouteUUpperRate j ((j : ℝ) / 80) +
        thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80) := by
  simp only [thetaCuspRouteUUpperRate, thetaCuspRouteUUpperRateSlope]
  ring

theorem thetaCuspRouteUUpperRateSlope_pos (j : ℕ) :
    0 < thetaCuspRouteUUpperRateSlope j := by
  have hpow : 1 ≤ thetaCuspRouteUExpStepLower ^ j :=
    one_le_pow₀ (by norm_num [thetaCuspRouteUExpStepLower])
  rw [thetaCuspRouteUUpperRateSlope]
  nlinarith

theorem thetaCuspRouteUUpperRate_endpoint_nonneg
    {j : ℕ} (hj : j < 80) :
    0 ≤ thetaCuspRouteUUpperRate j ((j : ℝ) / 80) := by
  interval_cases j <;>
    norm_num [thetaCuspRouteUUpperRate, thetaCuspRouteUExpStepLower]

theorem exp_neg_le_expNegTruncPoly_sixtyFive {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ (expNegTruncPoly 65).eval u := by
  rcases hu.eq_or_lt with rfl | hu
  · norm_num [eval_expNegTruncPoly, Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos (m := 65) (by norm_num) hu
    norm_num at h
    exact h.le

theorem exp_neg_le_thetaCuspRouteUExpNegTaylorEight {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ thetaCuspRouteUExpNegTaylorEight u := by
  rcases hu.eq_or_lt with rfl | hu
  · norm_num [thetaCuspRouteUExpNegTaylorEight, eval_expNegTruncPoly,
      Finset.sum_range_succ]
  · have h := expNegTruncPoly_sub_exp_oriented_pos (m := 9) (by norm_num) hu
    norm_num at h
    rw [thetaCuspRouteUExpNegTaylorEight]
    exact h.le

theorem thetaCuspRouteUUpperEndpoint_pos
    {j : ℕ} (hj : j < 80) : 0 < thetaCuspRouteUUpperEndpoint j := by
  have hz := thetaCuspRouteUUpperRate_endpoint_nonneg hj
  have h := exp_neg_le_expNegTruncPoly_sixtyFive hz
  rw [thetaCuspRouteUUpperEndpoint]
  exact (Real.exp_pos _).trans_le h

theorem thetaCuspRouteU_outer_upper :
    4 * Real.pi * Real.exp (-Real.pi) ≤ (0.543043 : ℝ) := by
  have hp : Real.pi ≤ (3.14159265358979323847 : ℝ) := Real.pi_lt_d20.le
  have he := exp_neg_pi_rationalEnclosure_upper
  have hmul := mul_le_mul hp he (Real.exp_pos _).le (by norm_num)
  nlinarith

theorem thetaCuspRouteUUpperCertificate_nonneg
    {r j : ℕ} (hj : j < 80) {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 80)) :
    0 ≤ thetaCuspRouteUUpperCertificate r j x := by
  have hx0 : 0 ≤ x := le_trans (by positivity : (0 : ℝ) ≤ (j : ℝ) / 80) hx.1
  have hgap : 0 ≤ x - (j : ℝ) / 80 := sub_nonneg.mpr hx.1
  have hu : 0 ≤ thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80) :=
    mul_nonneg (thetaCuspRouteUUpperRateSlope_pos j).le hgap
  have hprop : 0 ≤ thetaCuspRouteUExpNegTaylorEight
      (thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80)) :=
    (Real.exp_pos _).le.trans (exp_neg_le_thetaCuspRouteUExpNegTaylorEight hu)
  have hchord := exp_two_mul_le_thetaCuspRouteUExpChord hx
  have hinner : 0 ≤ thetaCuspRouteUUpperInnerIntercept j +
      thetaCuspRouteUUpperInnerSlope j * x := by
    rw [thetaCuspRouteUUpperInner_eq_chord]
    have : 1 ≤ thetaCuspRouteUExpChord j x :=
      (Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * x)).trans hchord
    nlinarith
  rw [thetaCuspRouteUUpperCertificate]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (thetaCuspRouteUUpperEndpoint_pos hj).le)
        (pow_nonneg hx0 r)) hinner) hprop

theorem density_le_thetaCuspRouteUUpperCertificate
    {r j : ℕ} (hj : j < 80) {x : ℝ}
    (hx : (j : ℝ) / 80 ≤ x ∧ x ≤ (((j + 1 : ℕ) : ℝ) / 80)) :
    2 * (x ^ r * thetaCuspSourceTerm x 1) ≤
      thetaCuspRouteUUpperCertificate r j x := by
  have hx0 : 0 ≤ x := le_trans (by positivity : (0 : ℝ) ≤ (j : ℝ) / 80) hx.1
  have hgap : 0 ≤ x - (j : ℝ) / 80 := sub_nonneg.mpr hx.1
  have hslope := thetaCuspRouteUUpperRateSlope_pos j
  have hu : 0 ≤ thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80) :=
    mul_nonneg hslope.le hgap
  have hrate := thetaCuspRouteUUpperRate_le_firstLiouvilleRate hx.1
  have haffine := thetaCuspRouteUUpperRate_affine j x
  have hendpoint := exp_neg_le_expNegTruncPoly_sixtyFive
    (thetaCuspRouteUUpperRate_endpoint_nonneg hj)
  have hprop := exp_neg_le_thetaCuspRouteUExpNegTaylorEight hu
  have hdecay : Real.exp (-thetaCuspFirstLiouvilleRate x) ≤
      thetaCuspRouteUUpperEndpoint j *
        thetaCuspRouteUExpNegTaylorEight
          (thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80)) := by
    calc
      _ ≤ Real.exp (-thetaCuspRouteUUpperRate j x) :=
        Real.exp_le_exp.mpr (neg_le_neg hrate)
      _ = Real.exp (-thetaCuspRouteUUpperRate j ((j : ℝ) / 80)) *
          Real.exp (-(thetaCuspRouteUUpperRateSlope j *
            (x - (j : ℝ) / 80))) := by
        rw [← Real.exp_add, haffine]
        congr 1
        ring
      _ ≤ thetaCuspRouteUUpperEndpoint j *
          thetaCuspRouteUExpNegTaylorEight
            (thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80)) := by
        rw [thetaCuspRouteUUpperEndpoint]
        exact mul_le_mul hendpoint hprop (Real.exp_pos _).le
          ((Real.exp_pos _).le.trans hendpoint)
  have hchord := exp_two_mul_le_thetaCuspRouteUExpChord hx
  have hinner :
      2 * Real.pi * Real.exp (2 * x) - 3 ≤
        thetaCuspRouteUUpperInnerIntercept j +
          thetaCuspRouteUUpperInnerSlope j * x := by
    rw [thetaCuspRouteUUpperInner_eq_chord]
    have hp : 2 * Real.pi ≤ (6.283186 : ℝ) := by nlinarith [Real.pi_lt_d20]
    calc
      _ ≤ (6.283186 : ℝ) * Real.exp (2 * x) - 3 := by gcongr
      _ ≤ (6.283186 : ℝ) * thetaCuspRouteUExpChord j x - 3 := by gcongr
  have hactualInner0 : 0 ≤ 2 * Real.pi * Real.exp (2 * x) - 3 := by
    have hone : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_gt_three]
  have hupperInner0 : 0 ≤ thetaCuspRouteUUpperInnerIntercept j +
      thetaCuspRouteUUpperInnerSlope j * x := hactualInner0.trans hinner
  have houter := thetaCuspRouteU_outer_upper
  rw [thetaCuspRouteUUpperCertificate,
    thetaCuspSourceTerm_one_eq_liouvilleGibbs,
    thetaCuspLiouvilleGibbsAtom_one_eq_rate]
  calc
    2 * (x ^ r *
        (2 * Real.pi * (2 * Real.pi * Real.exp (2 * x) - 3) *
          (Real.exp (-Real.pi) * Real.exp (-thetaCuspFirstLiouvilleRate x)))) =
      (4 * Real.pi * Real.exp (-Real.pi)) * x ^ r *
        (2 * Real.pi * Real.exp (2 * x) - 3) *
          Real.exp (-thetaCuspFirstLiouvilleRate x) := by ring
    _ ≤ (0.543043 : ℝ) * x ^ r *
        (2 * Real.pi * Real.exp (2 * x) - 3) *
          Real.exp (-thetaCuspFirstLiouvilleRate x) := by gcongr
    _ ≤ (0.543043 : ℝ) * x ^ r *
        (thetaCuspRouteUUpperInnerIntercept j +
          thetaCuspRouteUUpperInnerSlope j * x) *
          Real.exp (-thetaCuspFirstLiouvilleRate x) := by gcongr
    _ ≤ (0.543043 : ℝ) * thetaCuspRouteUUpperEndpoint j * x ^ r *
        (thetaCuspRouteUUpperInnerIntercept j +
          thetaCuspRouteUUpperInnerSlope j * x) *
          thetaCuspRouteUExpNegTaylorEight
            (thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80)) := by
      have hfactor : 0 ≤ (0.543043 : ℝ) * x ^ r *
          (thetaCuspRouteUUpperInnerIntercept j +
            thetaCuspRouteUUpperInnerSlope j * x) :=
        mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx0 r)) hupperInner0
      calc
        _ = ((0.543043 : ℝ) * x ^ r *
              (thetaCuspRouteUUpperInnerIntercept j +
                thetaCuspRouteUUpperInnerSlope j * x)) *
              Real.exp (-thetaCuspFirstLiouvilleRate x) := by ring
        _ ≤ ((0.543043 : ℝ) * x ^ r *
              (thetaCuspRouteUUpperInnerIntercept j +
                thetaCuspRouteUUpperInnerSlope j * x)) *
              (thetaCuspRouteUUpperEndpoint j *
                thetaCuspRouteUExpNegTaylorEight
                  (thetaCuspRouteUUpperRateSlope j * (x - (j : ℝ) / 80))) :=
          mul_le_mul_of_nonneg_left hdecay hfactor
        _ = _ := by ring

/-! ## Exact upper certificate integrals -/

def thetaCuspRouteUIntervalPowSubLeftMass (r m : ℕ) (a b : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    (m.choose q : ℝ) * (-a) ^ (m - q) *
      ((b ^ (r + q + 1) - a ^ (r + q + 1)) / (r + q + 1 : ℕ))

theorem intervalIntegral_pow_mul_sub_left_pow_eq_routeUMass
    (r m : ℕ) (a b : ℝ) :
    (∫ x in a..b, x ^ r * (x - a) ^ m) =
      thetaCuspRouteUIntervalPowSubLeftMass r m a b := by
  rw [show (fun x : ℝ => x ^ r * (x - a) ^ m) = fun x : ℝ =>
      ∑ q ∈ Finset.range (m + 1),
        ((m.choose q : ℝ) * (-a) ^ (m - q)) * x ^ (r + q) by
    funext x
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
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

def thetaCuspRouteUUpperTaylorMass (r j : ℕ) : ℝ :=
  let a : ℝ := (j : ℝ) / 80
  let b : ℝ := ((j + 1 : ℕ) : ℝ) / 80
  let k : ℝ := thetaCuspRouteUUpperRateSlope j
  thetaCuspRouteUUpperInnerIntercept j *
      ∑ m ∈ Finset.range 9,
        (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
          thetaCuspRouteUIntervalPowSubLeftMass r m a b +
    thetaCuspRouteUUpperInnerSlope j *
      ∑ m ∈ Finset.range 9,
        (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
          thetaCuspRouteUIntervalPowSubLeftMass (r + 1) m a b

def thetaCuspRouteUUpperIntervalMass (r j : ℕ) : ℝ :=
  (0.543043 : ℝ) * thetaCuspRouteUUpperEndpoint j *
    thetaCuspRouteUUpperTaylorMass r j

theorem intervalIntegral_thetaCuspRouteUUpperCertificate_eq_mass
    (r j : ℕ) :
    (∫ x in (j : ℝ) / 80..(((j + 1 : ℕ) : ℝ) / 80),
      thetaCuspRouteUUpperCertificate r j x) =
      thetaCuspRouteUUpperIntervalMass r j := by
  let a : ℝ := (j : ℝ) / 80
  let b : ℝ := ((j + 1 : ℕ) : ℝ) / 80
  let k : ℝ := thetaCuspRouteUUpperRateSlope j
  let A : ℝ := thetaCuspRouteUUpperInnerIntercept j
  let B : ℝ := thetaCuspRouteUUpperInnerSlope j
  have hfun : (fun x : ℝ =>
      x ^ r * (A + B * x) * thetaCuspRouteUExpNegTaylorEight (k * (x - a))) =
      fun x : ℝ =>
        A * ∑ m ∈ Finset.range 9,
            (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
              (x ^ r * (x - a) ^ m) +
          B * ∑ m ∈ Finset.range 9,
            (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
              (x ^ (r + 1) * (x - a) ^ m) := by
    funext x
    rw [thetaCuspRouteUExpNegTaylorEight, eval_expNegTruncPoly]
    simp_rw [mul_pow, pow_add]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [show (fun x : ℝ => thetaCuspRouteUUpperCertificate r j x) =
      fun x : ℝ => ((0.543043 : ℝ) * thetaCuspRouteUUpperEndpoint j) *
        (x ^ r * (A + B * x) *
          thetaCuspRouteUExpNegTaylorEight (k * (x - a))) by
    funext x
    simp only [thetaCuspRouteUUpperCertificate, A, B, k, a]
    ring]
  rw [intervalIntegral.integral_const_mul, hfun,
    intervalIntegral.integral_add
      (by exact (by fun_prop : Continuous (fun x : ℝ =>
        A * ∑ m ∈ Finset.range 9,
          (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
            (x ^ r * (x - a) ^ m))).intervalIntegrable _ _)
      (by exact (by fun_prop : Continuous (fun x : ℝ =>
        B * ∑ m ∈ Finset.range 9,
          (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
            (x ^ (r + 1) * (x - a) ^ m))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum, intervalIntegral.integral_finsetSum]
  · simp only [a, b]
    simp_rw [intervalIntegral.integral_const_mul,
      intervalIntegral_pow_mul_sub_left_pow_eq_routeUMass]
    simp only [thetaCuspRouteUUpperIntervalMass, thetaCuspRouteUUpperTaylorMass,
      A, B, k, a, b]
  · intro m hm
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
        (x ^ (r + 1) * (x - a) ^ m))).intervalIntegrable _ _
  · intro m hm
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (((-1 : ℝ) ^ m / (m.factorial : ℝ)) * k ^ m) *
        (x ^ r * (x - a) ^ m))).intervalIntegrable _ _

end

end RHTower
