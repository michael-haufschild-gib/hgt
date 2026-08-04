import GaloisForLFunctions.RHTower.CCMRadialProfileAsymptotic
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
def profileWeight (s x : ℝ) : ℝ := 1 / (Real.pi * Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)))

/-- Its derivative. -/
def profileWeightDeriv (s x : ℝ) : ℝ :=
  -(x * (2 * x ^ 2 - s - 1))
    / (Real.pi * ((x ^ 2 - 1) * (x ^ 2 - s)) * Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)))

theorem profileWeight_pos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) : 0 < profileWeight s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hP : (0 : ℝ) < Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) :=
    Real.sqrt_pos.mpr (mul_pos hd hn)
  rw [profileWeight]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  positivity

theorem hasDerivAt_profileWeight {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (profileWeight s) (profileWeightDeriv s x) x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos hd hn
  have hsP : (0 : ℝ) < Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := Real.sqrt_pos.mpr hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hinner : HasDerivAt (fun t : ℝ => (t ^ 2 - 1) * (t ^ 2 - s))
      (2 * x * (x ^ 2 - s) + (x ^ 2 - 1) * (2 * x)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 - s) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const s
    exact h1.fun_mul h2
  have hsqrt := hinner.sqrt hP.ne'
  have hmul := hsqrt.const_mul Real.pi
  have hinv := hmul.inv (by positivity)
  have hfun : profileWeight s = fun t : ℝ => (Real.pi * Real.sqrt ((t ^ 2 - 1) * (t ^ 2 - s)))⁻¹ := by
    funext t
    rw [profileWeight, one_div]
  have hval : -(Real.pi * ((2 * x * (x ^ 2 - s) + (x ^ 2 - 1) * (2 * x))
        / (2 * Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)))))
      / (Real.pi * Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) ^ 2
      = profileWeightDeriv s x := by
    obtain ⟨S, hS0, hSsq, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = (x ^ 2 - 1) * (x ^ 2 - s)
        ∧ Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) = S :=
      ⟨Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)), hsP, Real.mul_self_sqrt hP.le, rfl⟩
    rw [profileWeightDeriv, hSeq, ← hSsq]
    field_simp
    ring
  rw [hfun, ← hval]
  exact hinv

theorem profileWeightDeriv_nonpos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    profileWeightDeriv s x ≤ 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hP : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos hd hn
  have hsP : (0 : ℝ) < Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := Real.sqrt_pos.mpr hP
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnum : 0 ≤ x * (2 * x ^ 2 - s - 1) := by nlinarith
  rw [profileWeightDeriv, div_nonpos_iff]
  right
  refine ⟨by linarith, by positivity⟩

theorem continuousOn_profileWeightDeriv {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (profileWeightDeriv s) (Set.Ioi 1) := by
  have hden : ∀ x ∈ Set.Ioi (1 : ℝ),
      Real.pi * ((x ^ 2 - 1) * (x ^ 2 - s)) * Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) ≠ 0 := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
    have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
    have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
    have hsP : (0 : ℝ) < Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) :=
      Real.sqrt_pos.mpr (mul_pos hd hn)
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  rw [show profileWeightDeriv s = fun x : ℝ => -(x * (2 * x ^ 2 - s - 1))
      / (Real.pi * ((x ^ 2 - 1) * (x ^ 2 - s)) * Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) from by
    funext x
    rw [profileWeightDeriv]]
  refine ContinuousOn.div (by fun_prop) ?_ hden
  exact (continuousOn_const.mul (by fun_prop)).mul
    ((Real.continuous_sqrt.comp (by fun_prop)).continuousOn)

/-! ## The speed derivative is nonpositive -/

theorem xiSpeedDeriv_nonpos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) : xiSpeedDeriv s x ≤ 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
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

end GaloisForLFunctions.RHTower

end
