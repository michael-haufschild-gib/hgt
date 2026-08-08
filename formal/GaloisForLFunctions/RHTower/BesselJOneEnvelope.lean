import GaloisForLFunctions.RHTower.BesselJOneRecurrence

/-!
# The envelope decay of the Bessel function of order one

The order-one Bessel function has the integral representation
`J₁(u) = (1/π) ∫₀^π sin θ · sin(u sin θ) dθ`, which differs from the order-zero one only by the
amplitude `sin θ` in place of `1`.  The phase `u sin θ` is the same, so the same two van der Corput
blocks apply: on `[0, π/4]` the phase derivative `u cos θ` is bounded below and the first-derivative
test gives `O(1/u)`; on `[π/4, π/2]` the second derivative `u sin θ` is bounded below and the
second-derivative test gives `O(1/√u)`.

The only new ingredient is the amplitude budget: `sin` is bounded by one and its derivative is
bounded by one, so the budget of the two tests is bounded by a constant on a quarter period.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

/-- The amplitude of the order-one Bessel integral, as a complex-valued function. -/
def besselAmp (θ : ℝ) : ℂ := (Real.sin θ : ℂ)

theorem contDiff_besselAmp : ContDiff ℝ 1 besselAmp :=
  Complex.ofRealCLM.contDiff.comp Real.contDiff_sin

theorem deriv_besselAmp : deriv besselAmp = fun θ : ℝ => (Real.cos θ : ℂ) := by
  funext θ
  exact ((Real.hasDerivAt_sin θ).ofReal_comp).deriv

theorem norm_besselAmp_le_one (θ : ℝ) : ‖besselAmp θ‖ ≤ 1 := by
  rw [besselAmp, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩

theorem continuous_besselAmpIntegrand (u : ℝ) :
    Continuous fun θ : ℝ => besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) := by
  refine (Complex.continuous_ofReal.comp Real.continuous_sin).mul ?_
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp (by unfold besselPhase; fun_prop)

/-- The amplitude budget of the two van der Corput tests on an interval. -/
theorem besselAmp_budget_le {a b : ℝ} (hab : a ≤ b) :
    ‖besselAmp b‖ + ‖besselAmp a‖ + ∫ t in a..b, ‖deriv besselAmp t‖ ≤ 2 + (b - a) := by
  have hint1 : IntervalIntegrable (fun t : ℝ => ‖deriv besselAmp t‖) volume a b := by
    rw [deriv_besselAmp]
    exact ((Complex.continuous_ofReal.comp Real.continuous_cos).norm).intervalIntegrable _ _
  have h3 : (∫ t in a..b, ‖deriv besselAmp t‖) ≤ b - a := by
    have hmono : (∫ t in a..b, ‖deriv besselAmp t‖) ≤ ∫ _t in a..b, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hab hint1
        (intervalIntegrable_const) fun t _ => ?_
      rw [deriv_besselAmp, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
    simpa using hmono
  linarith [norm_besselAmp_le_one a, norm_besselAmp_le_one b]

/-- The real order-one integrand is minus the imaginary part of the complex phase integrand. -/
theorem integral_besselAmp_eq_neg_im (u a b : ℝ) :
    (∫ θ in a..b, Real.sin θ * Real.sin (u * Real.sin θ))
      = -(∫ θ in a..b, besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))).im := by
  have hint : IntervalIntegrable
      (fun θ : ℝ => besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))) volume a b :=
    (continuous_besselAmpIntegrand u).intervalIntegrable _ _
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (Complex.imCLM) hint
  rw [Complex.imCLM_apply] at h
  rw [← h, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have key : (besselAmp θ * Complex.exp (Complex.I * ((besselPhase u θ : ℝ) : ℂ))).im
      = Real.sin θ * Real.sin (besselPhase u θ) := by
    rw [besselAmp, mul_comm Complex.I, Complex.mul_im, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.imCLM_apply, key, besselPhase, Real.sin_neg]
  ring

/-- First van der Corput block for the order-one amplitude. -/
theorem norm_integral_besselAmp_first {u : ℝ} (hu : 0 < u) :
    ‖∫ θ in (0 : ℝ)..(Real.pi / 4),
        besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))‖
      ≤ 12 * Real.sqrt 2 / u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hab : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set lam : ℝ := u * (Real.sqrt 2 / 2) with hlam
  have hlampos : 0 < lam := by rw [hlam]; positivity
  have hnn : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 4), 0 ≤ deriv (deriv (besselPhase u)) t := by
    intro t ht
    rw [deriv_deriv_besselPhase]
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (le_trans ht.2 (by linarith))
    positivity
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 4), lam ≤ |deriv (besselPhase u) t| := by
    intro t ht
    rw [deriv_besselPhase]
    have hcos : Real.sqrt 2 / 2 ≤ Real.cos t := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi ht.1 (by linarith) ht.2
      rwa [Real.cos_pi_div_four] at h
    have hcosnn : (0 : ℝ) ≤ Real.cos t := le_trans (by positivity) hcos
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u * Real.cos t), hlam]
    exact mul_le_mul_of_nonneg_left hcos hu.le
  have h := _root_.RHTower.firstDerivTest (φ := besselPhase u) (A := besselAmp)
    hab hlampos (contDiff_besselPhase u) hnn hbound contDiff_besselAmp
  have hbud : ‖besselAmp (Real.pi / 4)‖ + ‖besselAmp 0‖
      + ∫ t in (0 : ℝ)..(Real.pi / 4), ‖deriv besselAmp t‖ ≤ 3 := by
    have := besselAmp_budget_le hab
    have hpi4 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_le_four]
    linarith
  have hstep : 4 * (‖besselAmp (Real.pi / 4)‖ + ‖besselAmp 0‖
      + ∫ t in (0 : ℝ)..(Real.pi / 4), ‖deriv besselAmp t‖) / lam ≤ 4 * 3 / lam := by
    gcongr
  refine le_trans (h.trans hstep) ?_
  rw [hlam, div_le_div_iff₀ (by positivity) hu]
  nlinarith [hs2pos, hs2, hu.le]

/-- Second van der Corput block for the order-one amplitude; this is the block that carries the
envelope. -/
theorem norm_integral_besselAmp_second {u : ℝ} (hu : 0 < u) :
    ‖∫ θ in (Real.pi / 4)..(Real.pi / 2),
        besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))‖
      ≤ 96 * Real.sqrt 2 / Real.sqrt u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hab : Real.pi / 4 ≤ Real.pi / 2 := by linarith
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmupos : (0 : ℝ) < u / 2 := by positivity
  have hbound : ∀ t ∈ Set.Icc (Real.pi / 4) (Real.pi / 2),
      u / 2 ≤ deriv (deriv (besselPhase u)) t := by
    intro t ht
    rw [deriv_deriv_besselPhase]
    have hsin : Real.sqrt 2 / 2 ≤ Real.sin t := by
      have h := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) ht.2 ht.1
      rwa [Real.sin_pi_div_four] at h
    have hhalf : (1 : ℝ) / 2 ≤ Real.sin t := le_trans (by nlinarith) hsin
    calc u / 2 = u * (1 / 2) := by ring
      _ ≤ u * Real.sin t := mul_le_mul_of_nonneg_left hhalf hu.le
  have h := _root_.RHTower.secondDerivTest (φ := besselPhase u) (A := besselAmp)
    hab hmupos (contDiff_besselPhase u) hbound contDiff_besselAmp
  have hbud : ‖besselAmp (Real.pi / 2)‖ + ‖besselAmp (Real.pi / 4)‖
      + ∫ t in (Real.pi / 4)..(Real.pi / 2), ‖deriv besselAmp t‖ ≤ 3 := by
    have := besselAmp_budget_le hab
    have hpi4 : Real.pi / 2 - Real.pi / 4 ≤ 1 := by linarith [Real.pi_le_four]
    linarith
  have hstep : 32 * (‖besselAmp (Real.pi / 2)‖ + ‖besselAmp (Real.pi / 4)‖
      + ∫ t in (Real.pi / 4)..(Real.pi / 2), ‖deriv besselAmp t‖) / Real.sqrt (u / 2)
      ≤ 32 * 3 / Real.sqrt (u / 2) := by
    gcongr
  refine le_trans (h.trans hstep) ?_
  have hsqrt : Real.sqrt (u / 2) = Real.sqrt u / Real.sqrt 2 := Real.sqrt_div hu.le 2
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  rw [hsqrt, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hupos]
  nlinarith [hs2, hs2pos, hupos.le]

/-- The half-period reduction of the order-one representation. -/
theorem besselJ1_eq_two_div_pi_mul (u : ℝ) :
    besselJ1 u
      = (2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ) := by
  have hcont := continuous_sin_mul_sin u
  have hsplit : (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ))
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ))
        + ∫ θ in (Real.pi / 2)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hrefl : (∫ θ in (Real.pi / 2)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => Real.sin θ * Real.sin (u * Real.sin θ)) Real.pi (a := 0) (b := Real.pi / 2)
    have hendpoints : Real.pi - Real.pi / 2 = Real.pi / 2 ∧ Real.pi - 0 = Real.pi := by
      constructor <;> ring
    rw [hendpoints.1, hendpoints.2] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [Real.sin_pi_sub]
  rw [besselJ1_eq_integral, hsplit, hrefl]
  ring

/-- **The order-one envelope bound.**  For `u ≥ 1` the Bessel function of order one decays like
`u^{-1/2}`, with the explicit constant `108 √2`. -/
theorem abs_besselJ1_le_envelope {u : ℝ} (hu : 1 ≤ u) :
    |besselJ1 u| ≤ 108 * Real.sqrt 2 / Real.sqrt u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hupos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun θ : ℝ => besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ))) volume a b :=
    fun a b => (continuous_besselAmpIntegrand u).intervalIntegrable a b
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)))
      = (∫ θ in (0 : ℝ)..(Real.pi / 4),
          besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)))
        + ∫ θ in (Real.pi / 4)..(Real.pi / 2),
            besselAmp θ * Complex.exp (Complex.I * (besselPhase u θ : ℂ)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hquarter : |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 108 * Real.sqrt 2 / Real.sqrt u := by
    rw [integral_besselAmp_eq_neg_im, abs_neg]
    refine le_trans (Complex.abs_im_le_norm _) ?_
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h1 := norm_integral_besselAmp_first hu0
    have h2 := norm_integral_besselAmp_second hu0
    have hfirst : 12 * Real.sqrt 2 / u ≤ 12 * Real.sqrt 2 / Real.sqrt u := by
      have := sqrt_le_self_of_one_le hu
      gcongr
    have hsum : 12 * Real.sqrt 2 / Real.sqrt u + 96 * Real.sqrt 2 / Real.sqrt u
        = 108 * Real.sqrt 2 / Real.sqrt u := by
      field_simp
      ring
    linarith [h1, h2, hfirst, hsum]
  have hfac : (2 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one hpi]
    linarith [Real.pi_gt_three]
  rw [besselJ1_eq_two_div_pi_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
  have habs : (0 : ℝ) ≤ |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)| :=
    abs_nonneg _
  calc (2 / Real.pi) * |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)|
      ≤ 1 * |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)| :=
        mul_le_mul_of_nonneg_right hfac habs
    _ = |∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ * Real.sin (u * Real.sin θ)| := one_mul _
    _ ≤ 108 * Real.sqrt 2 / Real.sqrt u := hquarter

/-- **The two-sided order-one envelope** `(44)`: `|J₁(u)| ≤ C·min(u, u^{-1/2})`, stated as the pair
of bounds that a split at `u = 1` consumes. -/
theorem abs_besselJ1_le_min {u : ℝ} (hu : 1 ≤ u) :
    |besselJ1 u| ≤ |u| / 2 ∧ |besselJ1 u| ≤ 108 * Real.sqrt 2 / Real.sqrt u :=
  ⟨abs_besselJ1_le u, abs_besselJ1_le_envelope hu⟩


end GaloisForLFunctions.RHTower
