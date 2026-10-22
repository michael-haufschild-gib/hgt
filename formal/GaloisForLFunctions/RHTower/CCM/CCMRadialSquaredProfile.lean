import GaloisForLFunctions.RHTower.CCM.CCMRadialProfileAsymptotic
import GaloisForLFunctions.RHTower.VanDerCorputWeightedAnti

/-!
# The squared radial profile

Squaring the profile of the previous file gives, with `cos²(v - pi/4) = (1 + sin 2v)/2`,

```text
(sqrt c A_s J_0(c xi_s))² = w_s(x) (1 + sin(2 c xi_s(x))) + errors,
     w_s(x) = 1/(pi sqrt((x²-1)(x²-s))),
```

so the non-oscillatory part is exactly the limiting density (up to the `s`-dependence of `w_s`) and the
oscillatory part is a weighted oscillatory integral.  Its weight `w_s` is positive and *decreasing*, and the
phase `2 c xi_s` has derivative `2 c xi_s' >= 2c` with `xi_s'' <= 0`, so the corpus weighted first-derivative
test with nonincreasing phase derivative applies directly and gives `O(1/c)`.

This file proves the oscillatory half.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## The density weight -/

/-- The `s`-dependent density weight `1/(pi sqrt((x²-1)(x²-s)))`.  At `s = 0` it is the limiting profile
density `1/(pi x sqrt(x²-1))`. -/
def profileWeight (s x : ℝ) : ℝ := 1 / (Real.pi * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))

/-- Its derivative. -/
def profileWeightDeriv (s x : ℝ) : ℝ :=
  -(x * (2 * x ^ (2 : ℕ) - s - 1))
    / (Real.pi * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))

theorem profileWeight_pos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) : 0 < profileWeight s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) :=
    Real.sqrt_pos.mpr (mul_pos hd hn)
  rw [profileWeight]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

theorem hasDerivAt_profileWeight {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (profileWeight s) (profileWeightDeriv s x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  have hsP : (0 : ℝ) < Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := Real.sqrt_pos.mpr hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hinner : HasDerivAt (fun t : ℝ => (t ^ (2 : ℕ) - 1) * (t ^ (2 : ℕ) - s))
      (2 * x * (x ^ (2 : ℕ) - s) + (x ^ (2 : ℕ) - 1) * (2 * x)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) - 1) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) - s) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const s
    exact h1.fun_mul h2
  have hsqrt := hinner.sqrt hP.ne'
  have hmul := hsqrt.const_mul Real.pi
  have hinv := hmul.inv (by positivity)
  have hfun : profileWeight s = fun t : ℝ => (Real.pi * Real.sqrt ((t ^ (2 : ℕ) - 1) * (t ^ (2 : ℕ) - s)))⁻¹ := by
    funext t
    rw [profileWeight, one_div]
  have hval : -(Real.pi * ((2 * x * (x ^ (2 : ℕ) - s) + (x ^ (2 : ℕ) - 1) * (2 * x))
        / (2 * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))))
      / (Real.pi * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) ^ (2 : ℕ)
      = profileWeightDeriv s x := by
    obtain ⟨S, hS0, hSsq, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)
        ∧ Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) = S :=
      ⟨Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)), hsP, Real.mul_self_sqrt hP.le, rfl⟩
    rw [profileWeightDeriv, hSeq, ← hSsq]
    field_simp
    ring
  rw [hfun, ← hval]
  exact hinv

theorem profileWeightDeriv_nonpos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    profileWeightDeriv s x ≤ 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  have hsP : (0 : ℝ) < Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := Real.sqrt_pos.mpr hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnum : 0 ≤ x * (2 * x ^ (2 : ℕ) - s - 1) := by nlinarith
  rw [profileWeightDeriv, div_nonpos_iff]
  right
  refine ⟨by linarith, by positivity⟩

theorem continuousOn_profileWeightDeriv {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (profileWeightDeriv s) (Set.Ioi 1) := by
  have hden : ∀ x ∈ Set.Ioi (1 : ℝ),
      Real.pi * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) ≠ 0 := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
    have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
    have hsP : (0 : ℝ) < Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) :=
      Real.sqrt_pos.mpr (mul_pos hd hn)
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  rw [show profileWeightDeriv s = fun x : ℝ => -(x * (2 * x ^ (2 : ℕ) - s - 1))
      / (Real.pi * ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) * Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s))) from by
    funext x
    rw [profileWeightDeriv]]
  refine ContinuousOn.div (by fun_prop) ?_ hden
  exact (continuousOn_const.mul (by fun_prop)).mul
    ((Real.continuous_sqrt.comp (by fun_prop)).continuousOn)

/-! ## The speed derivative is nonpositive -/

theorem xiSpeedDeriv_nonpos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) : xiSpeedDeriv s x ≤ 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  rw [xiSpeedDeriv, div_nonpos_iff]
  right
  refine ⟨by nlinarith, by positivity⟩

/-! ## The oscillatory half -/

/-- **The oscillatory part of the squared profile is `O(1/c)`.**  The weight `w_s` is positive and
decreasing, the phase `2 c xi_s` has derivative at least `2c` and nonincreasing derivative, so the corpus
weighted first-derivative test applies. -/
theorem abs_integral_profileWeight_mul_sin_le {s c α β : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hα : 1 < α) (hαβ : α ≤ β) (hc : 0 < c) :
    |∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)|
      ≤ 2 * profileWeight s α / c := by
  have hmem : ∀ x ∈ Set.uIcc α β, 1 < x := by
    intro x hx
    rw [Set.uIcc_of_le hαβ] at hx
    exact lt_of_lt_of_le hα hx.1
  -- the phase, shifted so that `sin` becomes `cos`
  have hg : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun t : ℝ => 2 * c * xiEndpointPhase s t - Real.pi / 2)
        (2 * c * xiSpeed s x) x := by
    intro x hx
    have h := (hasDerivAt_xiEndpointPhase hs0 (hmem x hx)).const_mul (2 * c)
    exact h.sub_const (Real.pi / 2)
  have hg' : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun t : ℝ => 2 * c * xiSpeed s t) (2 * c * xiSpeedDeriv s x) x := by
    intro x hx
    exact (hasDerivAt_xiSpeed (by linarith : s ≤ 1) (hmem x hx)).const_mul (2 * c)
  have hg''c : ContinuousOn (fun x : ℝ => 2 * c * xiSpeedDeriv s x) (Set.uIcc α β) := by
    refine continuousOn_const.mul ?_
    refine (continuousOn_xiSpeedDeriv (s := s) (by linarith)).mono ?_
    intro x hx
    exact hmem x hx
  have hg'lb : ∀ x ∈ Set.uIcc α β, 2 * c ≤ 2 * c * xiSpeed s x := by
    intro x hx
    have h1 := one_le_xiSpeed (s := s) (t := x) (by linarith) (hmem x hx)
    nlinarith [h1, hc]
  have hg''np : ∀ x ∈ Set.uIcc α β, 2 * c * xiSpeedDeriv s x ≤ 0 := by
    intro x hx
    have h := xiSpeedDeriv_nonpos hs1 (hmem x hx)
    nlinarith [h, hc]
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le_anti (a := α) (b := β) (lam := 2 * c)
    hαβ (by positivity)
    (w := profileWeight s) (w' := profileWeightDeriv s)
    (fun x hx => hasDerivAt_profileWeight hs1 (hmem x hx))
    ((continuousOn_profileWeightDeriv hs1).mono (fun x hx => hmem x hx))
    (fun x hx => (profileWeight_pos hs1 (hmem x hx)).le)
    (fun x hx => profileWeightDeriv_nonpos hs1 (hmem x hx))
    hg hg' hg''c hg'lb hg''np
  -- transfer to the real sine integral
  have hint : IntervalIntegrable (fun x : ℝ => ((profileWeight s x : ℝ) : ℂ)
      * Complex.exp (((2 * c * xiEndpointPhase s x - Real.pi / 2 : ℝ) : ℂ) * Complex.I))
      volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ ?_
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact fun x hx => (hasDerivAt_profileWeight hs1 (hmem x hx)).continuousAt.continuousWithinAt
    · refine Complex.continuous_exp.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ continuousOn_const
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact fun x hx =>
        ((hg x hx).continuousAt).continuousWithinAt
  have hcos := abs_integral_mul_cos_le_norm (w := profileWeight s)
    (g := fun x : ℝ => 2 * c * xiEndpointPhase s x - Real.pi / 2) (a := α) (b := β) hint
  have hsin : (∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x))
      = ∫ x in α..β, profileWeight s x
        * Real.cos (2 * c * xiEndpointPhase s x - Real.pi / 2) := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    show profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)
      = profileWeight s x * Real.cos (2 * c * xiEndpointPhase s x - Real.pi / 2)
    rw [Real.cos_sub_pi_div_two]
  rw [hsin]
  have hval : 4 * profileWeight s α / (2 * c) = 2 * profileWeight s α / c := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  calc |∫ x in α..β, profileWeight s x * Real.cos (2 * c * xiEndpointPhase s x - Real.pi / 2)|
      ≤ ‖∫ x in α..β, ((profileWeight s x : ℝ) : ℂ)
          * Complex.exp (((2 * c * xiEndpointPhase s x - Real.pi / 2 : ℝ) : ℂ) * Complex.I)‖ := hcos
    _ ≤ 4 * profileWeight s α / (2 * c) := hmain
    _ = 2 * profileWeight s α / c := hval


/-! ## The algebraic half -/

theorem profileWeight_zero_eq {x : ℝ} (hx : 1 < x) : profileWeight 0 x = profileDensity x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsplit : Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - 0)) = x * Real.sqrt (x ^ (2 : ℕ) - 1) := by
    rw [sub_zero, mul_comm, Real.sqrt_mul (by positivity), Real.sqrt_sq hx0.le]
  rw [profileWeight, profileDensity, hsplit]
  ring

theorem ampFourth_sq {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    ampFourth s x ^ (2 : ℕ) = 1 / Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  rw [ampFourth, div_pow, one_pow,
    Real.sq_sqrt (Real.sqrt_nonneg ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)))]

/-- The leading term squared is exactly the density times `1 + sin(2 c xi_s)`. -/
theorem model_sq_eq {s c x : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    (Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)) ^ (2 : ℕ)
      = profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x))) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := mul_pos hd hn
  have hsP : (0 : ℝ) < Real.sqrt ((x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s)) := Real.sqrt_pos.mpr hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT : Real.sqrt (2 / Real.pi) ^ (2 : ℕ) = 2 / Real.pi := Real.sq_sqrt (by positivity)
  have hq := ampFourth_sq hs1 hx
  have hcos : Real.cos (c * xiEndpointPhase s x - Real.pi / 4) ^ (2 : ℕ)
      = 1 / 2 + Real.sin (2 * (c * xiEndpointPhase s x)) / 2 := by
    rw [Real.cos_sq]
    have hval : 2 * (c * xiEndpointPhase s x - Real.pi / 4)
        = 2 * (c * xiEndpointPhase s x) - Real.pi / 2 := by ring
    rw [hval, Real.cos_sub_pi_div_two]
  rw [mul_pow, mul_pow, hT, hq, hcos, profileWeight]
  field_simp

/-- **The pointwise squared-profile identity with its error.**  Only the Bessel remainder enters. -/
theorem abs_profileSq_sub_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) (hcxi : 1 ≤ c * xiEndpointPhase s x) :
    |(Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)
        - profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x)))|
      ≤ (2 * Real.sqrt (2 / Real.pi) * ampFourth s x
          + 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)))
        * (5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))) := by
  have hT : (0 : ℝ) < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hamp : 0 < ampFourth s x := ampFourth_pos hs1 hx
  have hph : 0 < xiEndpointPhase s x := xiEndpointPhase_pos hs0 hs1 hx
  have hsv0 : (0 : ℝ) < Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hE1 : (0 : ℝ) ≤ 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
    positivity
  have hrem := abs_profile_sub_model_le hs0 hs1 hx hc hcxi
  have hmodel := model_sq_eq (s := s) (c := c) hs0 hs1 hx
  rw [← hmodel]
  -- write the difference of squares as a product
  have hfac : (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)
      - (Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)) ^ (2 : ℕ)
      = (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
          - Real.sqrt (2 / Real.pi) * ampFourth s x
            * Real.cos (c * xiEndpointPhase s x - Real.pi / 4))
        * (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
          + Real.sqrt (2 / Real.pi) * ampFourth s x
            * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)) := by
    ring
  rw [hfac, abs_mul, mul_comm]
  -- bound the sum factor
  have hMbound : |Real.sqrt (2 / Real.pi) * ampFourth s x
      * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ Real.sqrt (2 / Real.pi) * ampFourth s x := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt (2 / Real.pi) * ampFourth s x)]
    have hcos : |Real.cos (c * xiEndpointPhase s x - Real.pi / 4)| ≤ 1 :=
      Real.abs_cos_le_one _
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) * ampFourth s x)
      (by linarith : (0 : ℝ) ≤ 1 - |Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|)]
  have hsum : |Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
      + Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ 2 * Real.sqrt (2 / Real.pi) * ampFourth s x
        + 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
    have hsplit : Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
        + Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
        = (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
            - Real.sqrt (2 / Real.pi) * ampFourth s x
              * Real.cos (c * xiEndpointPhase s x - Real.pi / 4))
          + 2 * (Real.sqrt (2 / Real.pi) * ampFourth s x
            * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)) := by ring
    rw [hsplit]
    have htri := abs_add_le (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)
        - Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * xiEndpointPhase s x - Real.pi / 4))
      (2 * (Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)))
    have h2 : |2 * (Real.sqrt (2 / Real.pi) * ampFourth s x
        * Real.cos (c * xiEndpointPhase s x - Real.pi / 4))|
        = 2 * |Real.sqrt (2 / Real.pi) * ampFourth s x
          * Real.cos (c * xiEndpointPhase s x - Real.pi / 4)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [h2] at htri
    linarith [htri, hrem, hMbound]
  exact mul_le_mul hsum hrem (abs_nonneg _) (by positivity)



/-! ## Monotonicity of the error factors -/

theorem ampFourth_le_of_le {s α x : ℝ} (hs1 : s ≤ 1 / 2) (hα : 1 < α) (hαx : α ≤ x) :
    ampFourth s x ≤ ampFourth s α := by
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα
  have hx : 1 < x := lt_of_lt_of_le hα hαx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hdα : (0 : ℝ) < α ^ (2 : ℕ) - 1 := by nlinarith
  have hnα : (0 : ℝ) < α ^ (2 : ℕ) - s := by nlinarith
  have hle : (α ^ (2 : ℕ) - 1) * (α ^ (2 : ℕ) - s) ≤ (x ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) - s) := by
    have h1 : α ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by nlinarith
    nlinarith [h1, hdα, hnα]
  have hsα : 0 < Real.sqrt (Real.sqrt ((α ^ (2 : ℕ) - 1) * (α ^ (2 : ℕ) - s))) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hdα hnα))
  rw [ampFourth, ampFourth]
  refine div_le_div_of_nonneg_left (by norm_num) hsα ?_
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hle)

/-- **The squared-profile law on an interval.**  Equation `(10)` in quantitative form: the integral of the
squared profile over any interval inside `(1, ∞)` equals the integral of the density up to `O(1/c)` from the
oscillatory half and `O(c^{-1/4})` from the Bessel remainder. -/
theorem abs_integral_profileSq_sub_le {s c α β : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hα : 1 < α) (hαβ : α ≤ β) (hc : 0 < c) (hcxi : 1 ≤ c * xiEndpointPhase s α) :
    |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
        - ∫ x in α..β, profileWeight s x|
      ≤ 2 * profileWeight s α / c
        + (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
            + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
          * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) * (β - α) := by
  have hmem : ∀ x ∈ Set.uIcc α β, 1 < x ∧ α ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hαβ] at hx
    exact ⟨lt_of_lt_of_le hα hx.1, hx.1⟩
  have hcxix : ∀ x ∈ Set.uIcc α β, 1 ≤ c * xiEndpointPhase s x := by
    intro x hx
    obtain ⟨hx1, hαx⟩ := hmem x hx
    have hmono := xiEndpointPhase_le_of_le hs0 hs1 hα.le hαx
    have := mul_le_mul_of_nonneg_left hmono hc.le
    linarith
  have hxi : ContinuousOn (xiEndpointPhase s) (Set.uIcc α β) :=
    (continuousOn_xiEndpointPhase hs0).mono (fun x hx => (hmem x hx).1)
  have hphaseA : ContinuousOn (fun x : ℝ => c * xiEndpointPhase s x) (Set.uIcc α β) :=
    continuousOn_const.mul hxi
  have hphaseB : ContinuousOn (fun x : ℝ => 2 * c * xiEndpointPhase s x) (Set.uIcc α β) :=
    continuousOn_const.mul hxi
  have hphaseC : ContinuousOn (fun x : ℝ => 2 * (c * xiEndpointPhase s x)) (Set.uIcc α β) :=
    continuousOn_const.mul hphaseA
  -- continuity of the two integrands
  have hcontP : ContinuousOn
      (fun x : ℝ => (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
      (Set.uIcc α β) := by
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.mul (continuousOn_const.mul ?_) ?_
    · exact (continuousOn_xiAmplitude hs0 hs1).mono (fun x hx => (hmem x hx).1)
    · exact continuous_besselJ0.comp_continuousOn hphaseA
  have hcontW : ContinuousOn (profileWeight s) (Set.uIcc α β) :=
    fun x hx => (hasDerivAt_profileWeight hs1 (hmem x hx).1).continuousAt.continuousWithinAt
  have hcontS : ContinuousOn
      (fun x : ℝ => profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x))))
      (Set.uIcc α β) := by
    refine hcontW.mul ?_
    exact continuousOn_const.add (Real.continuous_sin.comp_continuousOn hphaseC)
  have hintP : IntervalIntegrable
      (fun x : ℝ => (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
      volume α β := hcontP.intervalIntegrable
  have hintW : IntervalIntegrable (profileWeight s) volume α β := hcontW.intervalIntegrable
  have hintS : IntervalIntegrable
      (fun x : ℝ => profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x))))
      volume α β := hcontS.intervalIntegrable
  have hintSin : IntervalIntegrable
      (fun x : ℝ => profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    exact hcontW.mul (Real.continuous_sin.comp_continuousOn hphaseB)
  -- split the model integral
  have hsplit : (∫ x in α..β, profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x))))
      = (∫ x in α..β, profileWeight s x)
        + ∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x) := by
    rw [← intervalIntegral.integral_add hintW hintSin]
    refine intervalIntegral.integral_congr ?_
    intro x _
    show profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x)))
      = profileWeight s x + profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)
    rw [show 2 * (c * xiEndpointPhase s x) = 2 * c * xiEndpointPhase s x from by ring]
    ring
  -- the pointwise error, bounded uniformly by its value at the left endpoint
  have hEmono : ∀ x ∈ Set.uIcc α β,
      (2 * Real.sqrt (2 / Real.pi) * ampFourth s x
          + 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)))
        * (5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)))
      ≤ (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
          + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
        * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) := by
    intro x hx
    obtain ⟨hx1, hαx⟩ := hmem x hx
    have hampx : ampFourth s x ≤ ampFourth s α := ampFourth_le_of_le hs1 hα hαx
    have hampα : 0 < ampFourth s α := ampFourth_pos hs1 hα
    have hphmono := xiEndpointPhase_le_of_le hs0 hs1 hα.le hαx
    have hsα : 0 < Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)) :=
      Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
    have hsle : Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))
        ≤ Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
      refine Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_left hphmono hc.le
    have hEx : 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))
        ≤ 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)) := by
      have e1 : 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))
          ≤ 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have e2 : 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))
          ≤ 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)) :=
        div_le_div_of_nonneg_left (by positivity) hsα hsle
      linarith
    have hT : (0 : ℝ) < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hExnn : (0 : ℝ) ≤ 5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
      have : 0 < ampFourth s x := ampFourth_pos hs1 hx1
      positivity
    refine mul_le_mul ?_ hEx hExnn (by positivity)
    have : 2 * Real.sqrt (2 / Real.pi) * ampFourth s x
        ≤ 2 * Real.sqrt (2 / Real.pi) * ampFourth s α :=
      mul_le_mul_of_nonneg_left hampx (by positivity)
    linarith [hEx, this]
  have hdiff : |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x
        * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
      - ∫ x in α..β, profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x)))|
      ≤ (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
          + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
        * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) * (β - α) := by
    rw [← intervalIntegral.integral_sub hintP hintS]
    have hbound : ∀ x ∈ Set.uIoc α β,
        ‖(Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)
          - profileWeight s x * (1 + Real.sin (2 * (c * xiEndpointPhase s x)))‖
        ≤ (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
            + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
          * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) := by
      intro x hx
      rw [Set.uIoc_of_le hαβ] at hx
      have hxmem : x ∈ Set.uIcc α β := by
        rw [Set.uIcc_of_le hαβ]
        exact ⟨hx.1.le, hx.2⟩
      have hx1 : 1 < x := (hmem x hxmem).1
      rw [Real.norm_eq_abs]
      exact le_trans (abs_profileSq_sub_le hs0 hs1 hx1 hc (hcxix x hxmem)) (hEmono x hxmem)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ β - α)] at h
  have hosc := abs_integral_profileWeight_mul_sin_le hs0 hs1 hα hαβ hc
  rw [hsplit] at hdiff
  have htri : |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x
        * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)) - ∫ x in α..β, profileWeight s x|
      ≤ |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x
          * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
        - ((∫ x in α..β, profileWeight s x)
          + ∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x))|
        + |∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)| := by
    have := abs_add_le
      ((∫ x in α..β, (Real.sqrt c * xiAmplitude s x
          * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
        - ((∫ x in α..β, profileWeight s x)
          + ∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)))
      (∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x))
    calc |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x
          * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)) - ∫ x in α..β, profileWeight s x|
        = |((∫ x in α..β, (Real.sqrt c * xiAmplitude s x
            * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
          - ((∫ x in α..β, profileWeight s x)
            + ∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x)))
          + (∫ x in α..β, profileWeight s x * Real.sin (2 * c * xiEndpointPhase s x))| := by
          congr 1
          ring
      _ ≤ _ := this
  linarith [htri, hdiff, hosc]



/-! ## From the `s`-dependent weight to the limiting density

`w_s = A-root²/pi`, so the `O(s)` bound on the fourth root transfers directly, and the limiting density is
`w_0`. -/

theorem profileWeight_eq_ampFourth_sq {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    profileWeight s x = ampFourth s x ^ (2 : ℕ) / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [ampFourth_sq hs1 hx, profileWeight]
  field_simp

/-- **The `s`-dependence of the density is linear.** -/
theorem abs_profileWeight_sub_density_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |profileWeight s x - profileDensity x| ≤ 3 * s * profileDensity x / (x ^ (2 : ℕ) - s) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hq0 : 0 < ampFourth 0 x := ampFourth_pos (by norm_num) hx
  have hqs : 0 < ampFourth s x := ampFourth_pos hs1 hx
  have hdiff := abs_ampFourth_sub_le hs0 hs1 hx
  have hsmall : s * ampFourth 0 x / (x ^ (2 : ℕ) - s) ≤ ampFourth 0 x := by
    rw [div_le_iff₀ hn]
    nlinarith [hq0, hn, hs0, hs1, hx0, hd]
  have hqsle : ampFourth s x ≤ 2 * ampFourth 0 x := by
    have h := abs_le.mp hdiff
    linarith [h.2, hsmall]
  have hw : profileWeight s x - profileDensity x
      = (ampFourth s x - ampFourth 0 x) * (ampFourth s x + ampFourth 0 x) / Real.pi := by
    rw [profileWeight_eq_ampFourth_sq hs1 hx, ← profileWeight_zero_eq hx,
      profileWeight_eq_ampFourth_sq (by norm_num) hx]
    field_simp
    ring
  rw [hw, abs_div, abs_mul, abs_of_pos hpi]
  have hsum : |ampFourth s x + ampFourth 0 x| ≤ 3 * ampFourth 0 x := by
    rw [abs_of_pos (by positivity)]
    linarith [hqsle]
  have hprod : |ampFourth s x - ampFourth 0 x| * |ampFourth s x + ampFourth 0 x|
      ≤ (s * ampFourth 0 x / (x ^ (2 : ℕ) - s)) * (3 * ampFourth 0 x) :=
    mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
  have hval : (s * ampFourth 0 x / (x ^ (2 : ℕ) - s)) * (3 * ampFourth 0 x) / Real.pi
      = 3 * s * profileDensity x / (x ^ (2 : ℕ) - s) := by
    rw [← profileWeight_zero_eq hx, profileWeight_eq_ampFourth_sq (by norm_num) hx]
    field_simp
  calc |ampFourth s x - ampFourth 0 x| * |ampFourth s x + ampFourth 0 x| / Real.pi
      ≤ (s * ampFourth 0 x / (x ^ (2 : ℕ) - s)) * (3 * ampFourth 0 x) / Real.pi :=
        div_le_div_of_nonneg_right hprod hpi.le
    _ = 3 * s * profileDensity x / (x ^ (2 : ℕ) - s) := hval

theorem profileDensity_le_of_le {α x : ℝ} (hα : 1 < α) (hαx : α ≤ x) :
    profileDensity x ≤ profileDensity α := by
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα
  have hx : 1 < x := lt_of_lt_of_le hα hαx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hdα : (0 : ℝ) < α ^ (2 : ℕ) - 1 := by nlinarith
  have hdx : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have hsα : (0 : ℝ) < Real.sqrt (α ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hdα
  have hsx : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hdx
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hle : Real.sqrt (α ^ (2 : ℕ) - 1) ≤ Real.sqrt (x ^ (2 : ℕ) - 1) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith
  rw [profileDensity, profileDensity]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  have h1 : Real.pi * α * Real.sqrt (α ^ (2 : ℕ) - 1) ≤ Real.pi * x * Real.sqrt (α ^ (2 : ℕ) - 1) := by
    nlinarith [mul_nonneg (mul_nonneg hpi.le (by linarith : (0 : ℝ) ≤ x - α)) hsα.le]
  have h2 : Real.pi * x * Real.sqrt (α ^ (2 : ℕ) - 1) ≤ Real.pi * x * Real.sqrt (x ^ (2 : ℕ) - 1) := by
    nlinarith [mul_nonneg (mul_nonneg hpi.le hx0.le)
      (by linarith : (0 : ℝ) ≤ Real.sqrt (x ^ (2 : ℕ) - 1) - Real.sqrt (α ^ (2 : ℕ) - 1))]
  linarith

/-- **The squared-profile law against the limiting density.**  Equation `(10)` with the limiting density
`1/(pi x sqrt(x²-1))` in place of the `s`-dependent weight: the extra cost is `O(s)`, hence `O(1/c)` under the
separation law. -/
theorem abs_integral_profileSq_sub_density_le {s c α β : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hα : 1 < α) (hαβ : α ≤ β) (hc : 0 < c) (hcxi : 1 ≤ c * xiEndpointPhase s α) :
    |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
        - ∫ x in α..β, profileDensity x|
      ≤ 2 * profileWeight s α / c
        + (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
            + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
          * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) * (β - α)
        + 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) * (β - α) := by
  have hmem : ∀ x ∈ Set.uIcc α β, 1 < x ∧ α ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hαβ] at hx
    exact ⟨lt_of_lt_of_le hα hx.1, hx.1⟩
  have hprev := abs_integral_profileSq_sub_le hs0 hs1 hα hαβ hc hcxi
  -- the density comparison
  have hcontW : ContinuousOn (profileWeight s) (Set.uIcc α β) :=
    fun x hx => (hasDerivAt_profileWeight hs1 (hmem x hx).1).continuousAt.continuousWithinAt
  have hcontD : ContinuousOn profileDensity (Set.uIcc α β) := by
    have : ∀ x ∈ Set.uIcc α β, profileDensity x = profileWeight 0 x :=
      fun x hx => (profileWeight_zero_eq (hmem x hx).1).symm
    refine ContinuousOn.congr ?_ this
    exact fun x hx =>
      ((hasDerivAt_profileWeight (by norm_num) (hmem x hx).1).continuousAt).continuousWithinAt
  have hintW : IntervalIntegrable (profileWeight s) volume α β := hcontW.intervalIntegrable
  have hintD : IntervalIntegrable profileDensity volume α β := hcontD.intervalIntegrable
  have hcmp : |(∫ x in α..β, profileWeight s x) - ∫ x in α..β, profileDensity x|
      ≤ 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) * (β - α) := by
    rw [← intervalIntegral.integral_sub hintW hintD]
    have hbound : ∀ x ∈ Set.uIoc α β,
        ‖profileWeight s x - profileDensity x‖ ≤ 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) := by
      intro x hx
      rw [Set.uIoc_of_le hαβ] at hx
      have hxmem : x ∈ Set.uIcc α β := by
        rw [Set.uIcc_of_le hαβ]
        exact ⟨hx.1.le, hx.2⟩
      obtain ⟨hx1, hαx⟩ := hmem x hxmem
      have hnα : (0 : ℝ) < α ^ (2 : ℕ) - s := by nlinarith [hα]
      have hnx : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith [hx1]
      have hdens : profileDensity x ≤ profileDensity α := profileDensity_le_of_le hα hαx
      have hdens0 : 0 < profileDensity x := by
        have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
        have hdx : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
        have hsx : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr hdx
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        rw [profileDensity]
        positivity
      rw [Real.norm_eq_abs]
      refine le_trans (abs_profileWeight_sub_density_le hs0 hs1 hx1) ?_
      have hnum : 3 * s * profileDensity x ≤ 3 * s * profileDensity α := by nlinarith [hdens, hs0]
      have hstep1 : 3 * s * profileDensity x / (x ^ (2 : ℕ) - s)
          ≤ 3 * s * profileDensity α / (x ^ (2 : ℕ) - s) :=
        div_le_div_of_nonneg_right hnum hnx.le
      have hstep2 : 3 * s * profileDensity α / (x ^ (2 : ℕ) - s)
          ≤ 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) := by
        refine div_le_div_of_nonneg_left
          (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * s) (profileDensity_nonneg hα.le)) hnα ?_
        nlinarith [hαx, hα]
      linarith
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ β - α)] at h
  have htri : |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x
        * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)) - ∫ x in α..β, profileDensity x|
      ≤ |(∫ x in α..β, (Real.sqrt c * xiAmplitude s x
          * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)) - ∫ x in α..β, profileWeight s x|
        + |(∫ x in α..β, profileWeight s x) - ∫ x in α..β, profileDensity x| :=
    abs_sub_le _ _ _
  linarith [htri, hprev, hcmp]



/-! ## From intervals to test functions

The interval bound holds uniformly in the right endpoint, so the primitive of the difference is uniformly
small.  One integration by parts against a test function converts that into the weak form of `(10)`: no
approximation argument is needed, only the fundamental theorem. -/

/-- The difference between the squared profile and the limiting density. -/
def profileDiff (s c x : ℝ) : ℝ :=
  (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ) - profileDensity x

/-- The error of the interval form of `(10)`. -/
def profileSqError (s c α β : ℝ) : ℝ :=
  2 * profileWeight s α / c
    + (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
        + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
      * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) * (β - α)
    + 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) * (β - α)

theorem continuousOn_profileDiff {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (profileDiff s c) (Set.Ioi 1) := by
  have hxi : ContinuousOn (xiEndpointPhase s) (Set.Ioi 1) := continuousOn_xiEndpointPhase hs0
  have hP : ContinuousOn
      (fun x : ℝ => (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
      (Set.Ioi 1) := by
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.mul (continuousOn_const.mul (continuousOn_xiAmplitude hs0 hs1)) ?_
    exact continuous_besselJ0.comp_continuousOn (continuousOn_const.mul hxi)
  have hD : ContinuousOn profileDensity (Set.Ioi 1) := by
    have heq : ∀ x ∈ Set.Ioi (1 : ℝ), profileDensity x = profileWeight 0 x :=
      fun x hx => (profileWeight_zero_eq hx).symm
    refine ContinuousOn.congr ?_ heq
    exact fun x hx =>
      ((hasDerivAt_profileWeight (by norm_num) hx).continuousAt).continuousWithinAt
  rw [show profileDiff s c = fun x : ℝ =>
      (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)
        - profileDensity x from by
    funext x
    rw [profileDiff]]
  exact hP.sub hD

theorem profileSqError_nonneg {s c α β : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hα : 1 < α)
    (hαβ : α ≤ β) (hc : 0 < c) : 0 ≤ profileSqError s c α β := by
  have hw : 0 < profileWeight s α := profileWeight_pos hs1 hα
  have hamp : 0 < ampFourth s α := ampFourth_pos hs1 hα
  have hpd : 0 ≤ profileDensity α := profileDensity_nonneg hα.le
  have hn : (0 : ℝ) < α ^ (2 : ℕ) - s := by nlinarith
  have hT : (0 : ℝ) < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)) := Real.sqrt_nonneg _
  have hβα : (0 : ℝ) ≤ β - α := by linarith
  rw [profileSqError]
  have h1 : 0 ≤ 2 * profileWeight s α / c := by positivity
  have h2 : 0 ≤ (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
      + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
    * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) * (β - α) := by
    have hA : 0 ≤ 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)) := by
      positivity
    have hB : 0 ≤ 2 * Real.sqrt (2 / Real.pi) * ampFourth s α := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt (2 / Real.pi) * ampFourth s α
      + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) hA
    exact mul_nonneg this hβα
  have h3 : 0 ≤ 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) * (β - α) := by
    have : 0 ≤ 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) := by positivity
    exact mul_nonneg this hβα
  linarith

/-- The interval bound, in the packaged form and uniform in the right endpoint. -/
theorem abs_integral_profileDiff_le {s c α β t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hα : 1 < α) (hαt : α ≤ t) (htβ : t ≤ β) (hc : 0 < c)
    (hcxi : 1 ≤ c * xiEndpointPhase s α) :
    |∫ x in α..t, profileDiff s c x| ≤ profileSqError s c α β := by
  have hcontD : ContinuousOn (profileDiff s c) (Set.Ioi 1) := continuousOn_profileDiff hs0 hs1
  have hsub : Set.uIcc α t ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hαt]
    intro x hx
    exact lt_of_lt_of_le hα hx.1
  have hint : IntervalIntegrable (profileDiff s c) volume α t :=
    (hcontD.mono hsub).intervalIntegrable
  have hcontP : ContinuousOn
      (fun x : ℝ => (Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ))
      (Set.uIcc α t) := by
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.mul (continuousOn_const.mul
      ((continuousOn_xiAmplitude hs0 hs1).mono hsub)) ?_
    exact continuous_besselJ0.comp_continuousOn
      (continuousOn_const.mul ((continuousOn_xiEndpointPhase hs0).mono hsub))
  have hcontDens : ContinuousOn profileDensity (Set.uIcc α t) := by
    have heq : ∀ x ∈ Set.uIcc α t, profileDensity x = profileWeight 0 x :=
      fun x hx => (profileWeight_zero_eq (hsub hx)).symm
    refine ContinuousOn.congr ?_ heq
    exact fun x hx =>
      ((hasDerivAt_profileWeight (by norm_num) (hsub hx)).continuousAt).continuousWithinAt
  have hsplit : (∫ x in α..t, profileDiff s c x)
      = (∫ x in α..t, (Real.sqrt c * xiAmplitude s x
          * besselJ0 (c * xiEndpointPhase s x)) ^ (2 : ℕ)) - ∫ x in α..t, profileDensity x := by
    rw [← intervalIntegral.integral_sub hcontP.intervalIntegrable hcontDens.intervalIntegrable]
    refine intervalIntegral.integral_congr ?_
    intro x _
    rw [profileDiff]
  rw [hsplit]
  have hmain := abs_integral_profileSq_sub_density_le hs0 hs1 hα hαt hc hcxi
  refine le_trans hmain ?_
  rw [profileSqError]
  have hamp : 0 < ampFourth s α := ampFourth_pos hs1 hα
  have hpd : 0 ≤ profileDensity α := profileDensity_nonneg hα.le
  have hn : (0 : ℝ) < α ^ (2 : ℕ) - s := by nlinarith
  have hT : (0 : ℝ) < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hA : 0 ≤ 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)) := by
    positivity
  have hfac : 0 ≤ (2 * Real.sqrt (2 / Real.pi) * ampFourth s α
      + 5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α)))
    * (5 * ampFourth s α / Real.sqrt (Real.sqrt (c * xiEndpointPhase s α))) := by
    refine mul_nonneg ?_ hA
    have : 0 ≤ 2 * Real.sqrt (2 / Real.pi) * ampFourth s α := by positivity
    linarith
  have hdfac : 0 ≤ 3 * s * profileDensity α / (α ^ (2 : ℕ) - s) := by positivity
  have h1 : (t - α) ≤ (β - α) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hfac, mul_le_mul_of_nonneg_left h1 hdfac]



/-- **The weak form of `(10)`.**  For any test function with a continuous derivative on `[α, β]`,

```text
|int_α^β phi(x) (P(x)² - density(x)) dx| <= (|phi(β)| + int_α^β |phi'|) · profileSqError,
```

so the squared profile converges weakly to the limiting density: the right-hand side is `O(1/c)` plus
`O(c^{-1/4})` for every fixed test function.  Only the fundamental theorem is used — the interval bound is
uniform in the right endpoint, so the primitive of the difference is uniformly small and one integration by
parts transfers that to the test function. -/
theorem abs_integral_testFunction_profileDiff_le {s c α β : ℝ} {φ φ' : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hα : 1 < α) (hαβ : α ≤ β) (hc : 0 < c)
    (hcxi : 1 ≤ c * xiEndpointPhase s α)
    (hφ : ∀ x ∈ Set.uIcc α β, HasDerivAt φ (φ' x) x)
    (hφ'c : ContinuousOn φ' (Set.uIcc α β)) :
    |∫ x in α..β, φ x * profileDiff s c x|
      ≤ (|φ β| + ∫ x in α..β, |φ' x|) * profileSqError s c α β := by
  have hM : 0 ≤ profileSqError s c α β := profileSqError_nonneg hs0 hs1 hα hαβ hc
  have hsub : Set.uIcc α β ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hαβ]
    intro x hx
    exact lt_of_lt_of_le hα hx.1
  have hcontD : ContinuousOn (profileDiff s c) (Set.Ioi 1) := continuousOn_profileDiff hs0 hs1
  have hDint : IntervalIntegrable (profileDiff s c) volume α β :=
    (hcontD.mono hsub).intervalIntegrable
  -- the primitive
  have hF : ∀ t ∈ Set.uIcc α β,
      HasDerivAt (fun u : ℝ => ∫ x in α..u, profileDiff s c x) (profileDiff s c t) t := by
    intro t ht
    have htIoi : t ∈ Set.Ioi (1 : ℝ) := hsub ht
    have hsubt : Set.uIcc α t ⊆ Set.Ioi 1 := by
      rw [Set.uIcc_of_le (by rw [Set.uIcc_of_le hαβ] at ht; exact ht.1)]
      intro x hx
      exact lt_of_lt_of_le hα hx.1
    have hintt : IntervalIntegrable (profileDiff s c) volume α t :=
      (hcontD.mono hsubt).intervalIntegrable
    have hnhds : Set.Ioi (1 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds htIoi
    have hmeas : StronglyMeasurableAtFilter (profileDiff s c) (nhds t) :=
      hcontD.stronglyMeasurableAtFilter isOpen_Ioi t htIoi
    exact intervalIntegral.integral_hasDerivAt_right hintt hmeas (hcontD.continuousAt hnhds)
  have hFcont : ContinuousOn (fun u : ℝ => ∫ x in α..u, profileDiff s c x) (Set.uIcc α β) :=
    fun t ht => ((hF t ht).continuousAt).continuousWithinAt
  have hφ'int : IntervalIntegrable φ' volume α β := hφ'c.intervalIntegrable
  -- integration by parts
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := φ) (u' := φ')
    (v := fun u : ℝ => ∫ x in α..u, profileDiff s c x) (v' := profileDiff s c)
    (a := α) (b := β) hφ hF hφ'int hDint
  have hzero : (∫ x in α..α, profileDiff s c x) = 0 := intervalIntegral.integral_same
  rw [hzero, mul_zero, sub_zero] at hIBP
  rw [hIBP]
  -- bound the two pieces
  have hFβ : |∫ x in α..β, profileDiff s c x| ≤ profileSqError s c α β :=
    abs_integral_profileDiff_le hs0 hs1 hα hαβ (le_refl β) hc hcxi
  have hb1 : |φ β * ∫ x in α..β, profileDiff s c x| ≤ |φ β| * profileSqError s c α β := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hFβ (abs_nonneg _)
  have hprodint : IntervalIntegrable
      (fun x : ℝ => φ' x * ∫ y in α..x, profileDiff s c y) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    exact hφ'c.mul hFcont
  have habsint : IntervalIntegrable (fun x : ℝ => |φ' x| * profileSqError s c α β) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (hφ'c.abs).mul continuousOn_const
  have hb2 : |∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y|
      ≤ (∫ x in α..β, |φ' x|) * profileSqError s c α β := by
    have hstep : |∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y|
        ≤ ∫ x in α..β, |φ' x| * profileSqError s c α β := by
      have h1 : |∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y|
          ≤ ∫ x in α..β, |φ' x * ∫ y in α..x, profileDiff s c y| := by
        have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x : ℝ => φ' x * ∫ y in α..x, profileDiff s c y) hαβ
        simpa [Real.norm_eq_abs] using h
      have h2 : (∫ x in α..β, |φ' x * ∫ y in α..x, profileDiff s c y|)
          ≤ ∫ x in α..β, |φ' x| * profileSqError s c α β := by
        refine intervalIntegral.integral_mono_on hαβ hprodint.abs habsint ?_
        intro x hx
        have hxmem : x ∈ Set.uIcc α β := by
          rw [Set.uIcc_of_le hαβ]
          exact hx
        have hFx : |∫ y in α..x, profileDiff s c y| ≤ profileSqError s c α β :=
          abs_integral_profileDiff_le hs0 hs1 hα hx.1 hx.2 hc hcxi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hFx (abs_nonneg _)
      linarith
    have hconstmul : (∫ x in α..β, |φ' x| * profileSqError s c α β)
        = (∫ x in α..β, |φ' x|) * profileSqError s c α β := by
      rw [intervalIntegral.integral_mul_const]
    linarith [hstep, hconstmul.le, hconstmul.ge]
  have htri : |φ β * (∫ x in α..β, profileDiff s c x)
      - ∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y|
      ≤ |φ β * ∫ x in α..β, profileDiff s c x|
        + |∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y| := by
    have := abs_add_le (φ β * (∫ x in α..β, profileDiff s c x))
      (-(∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y))
    rw [abs_neg] at this
    calc |φ β * (∫ x in α..β, profileDiff s c x)
        - ∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y|
        = |φ β * (∫ x in α..β, profileDiff s c x)
          + -(∫ x in α..β, φ' x * ∫ y in α..x, profileDiff s c y)| := by
          rw [sub_eq_add_neg]
      _ ≤ _ := this
  have hexp : (|φ β| + ∫ x in α..β, |φ' x|) * profileSqError s c α β
      = |φ β| * profileSqError s c α β
        + (∫ x in α..β, |φ' x|) * profileSqError s c α β := by ring
  rw [hexp]
  linarith [htri, hb1, hb2]


end GaloisForLFunctions.RHTower

end
