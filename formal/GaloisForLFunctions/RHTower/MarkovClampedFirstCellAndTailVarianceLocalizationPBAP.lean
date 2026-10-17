import GaloisForLFunctions.RHTower.MarkovMultiStagePotentialAndAllRatioSinhCrossoverPBAP

/-!
# Clamped Rational-Resolvent First-Cell Quadrature Bounds and Tail-Cell Variance Localization

This module executes **Option 2** of the `CHMD + HF + EWU` synthesis (`docs/notes.md`), resolving the
high-frequency divergence of the Taylor parabola lower bound
`-(7 / 480) * r ^ 2 ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x`
by exploiting the exact `(1 / 4 + r ^ 2)` resolvent denominator in
`neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq`.

## Mathematical Overview

1. **Exact Sum-of-Squares (SOS) Completion on the First-Cell Numerator (`neg_sqrt_two_mul_sin_sub_mul_one_sub_cos_le`)**:
   - In `neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq`,
     $$-\left(\frac{1}{4} + r^2\right) I_2(r)
       = 2(\sqrt{2}-1)r^2 - \sqrt{2}r\sin(r\log 2)
         + \left(\frac{2\sqrt{2}-1}{3} - \frac{4-2\sqrt{2}}{3}r^2\right)(1 - \cos(r\log 2)).$$
   - Because $\sin^2\theta + (1 - \cos\theta)^2 = 2(1 - \cos\theta)$, the linear-in-$r$ term
     $-\sqrt{2}r\sin(r\log 2)$ is absorbed into the negative quadratic term
     $-\frac{4-2\sqrt{2}}{3}r^2(1 - \cos(r\log 2))$ via the exact SOS identity
     $$\frac{1}{c} - \bigl(-\sqrt{2}r\sin\theta - c r^2(1 - \cos\theta)\bigr)
       = \frac{(c r\sin\theta + \sqrt{2})^2}{2c} + \frac{c}{2}r^2(1 - \cos\theta)^2 \ge 0$$
     for $c = (4 - 2\sqrt{2}) / 3 > 0$, where $1 / c = 3(2 + \sqrt{2}) / 4$.
   - Dividing by $1 / 4 + r^2 > 0$ gives the **Global Rational-Resolvent Lower Bound on $I_2(r)$**
     (`neg_two_sqrt_two_sub_one_sub_resolvent_le_integral_one_two_cosLogProfile`,
     `neg_rational_sub_resolvent_le_integral_one_two_cosLogProfile`):
     $$\forall r \in \mathbb{R},\qquad
       -2(\sqrt{2}-1) - \frac{(16 + 19\sqrt{2}) / 12}{1/4 + r^2} \le I_2(r),
       \qquad
       -\frac{169}{204} - \frac{18 / 5}{1/4 + r^2} \le I_2(r).$$

2. **Global Uniform and Clamped Two-Regime First-Cell Bounds (`-91 / 100` and `-min ((7/480)r²) (91/100)`)**:
   - Combining `r² ≤ 49` (`-I_2(r) ≤ (7/480) r² ≤ 343/480 < 91/100`) with `49 ≤ r²`
     (`-I_2(r) ≤ 169/204 + (18/5)/(197/4) < 91/100`) establishes the **Global Uniform First-Cell
     Lower Bound** (`neg_ninety_one_hundredths_le_integral_one_two_cosLogProfile`) and the
     **Clamped Two-Regime Bound** (`neg_min_seven_four_eightieths_sq_ninety_one_hundredths_le_integral_one_two_cosLogProfile`):
     $$\forall r \in \mathbb{R},\qquad
       -\min\left(\frac{7}{480}r^2,\,\frac{91}{100}\right) \le I_2(r).$$

3. **$S(f)$-Free Spectral Integration on the First Cell `[1, 2]`**:
   - Integrating the rational-resolvent and clamped bounds against $\frac{1}{2\pi}\|F(r)\|^2$ yields
     lower bounds on the first-cell quadrature integral $\int_1^2 \frac{C_f(x)-\operatorname{cellSecant}(C_f,2,x)}{\sqrt{x}}\,dx$
     that depend **only** on $\int \|f\|^2$ and $\operatorname{bochnerResolventEnergy}(k_f)$ with
     **zero `spectralSecondMoment` ($S(f)$) growth**
     (`neg_four_sqrt_two_sub_one_l2_sub_resolvent_le_integral_one_two`,
     `neg_ninety_one_fiftieths_l2_le_integral_one_two`,
     `neg_min_first_cell_le_integral_one_two`).

4. **$S(F)$-Free Tail-Cell (`n ≥ 3`) Variance Localization and Clamped All-Ratio Conservation / `markovEnergy ≥ 0` Laws**:
   - Combining the $S(F)$-free rational-resolvent first-cell bound with the exact Euler–Maclaurin
     conservation law on `coshHalfMoment f = 0` and `logVector F = 0` proves **Tail-Cell ($n \ge 3$)
     Variance Localization** (`tail_cell_variance_localization_of_cosh_zero_of_logVector_eq_zero`),
     eliminating `spectralSecondMoment F` completely from the first cell $n = 2$.
   - Replacing $(7 / 480) S(f)$ by $\min((7 / 480) S(f), (91 / 50) L(f))$ in
     `secantNumeratorCellDefect` yields the **Clamped All-Ratio Conservation and `markovEnergy ≥ 0` Laws**
     (`clamped_all_ratio_conservation_bound_of_cosh_zero`,
     `clamped_all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate ContDiff FourierTransform BigOperators
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Exact SOS Completion on the First-Cell Numerator and the Global Rational-Resolvent Bound on `I_2(r)` -/

/-- **Exact Trigonometric Sum-of-Squares (SOS) Bound**:
since `sin² θ + (1 - cos θ)² = 2(1 - cos θ)`, for any `c > 0` and any `r, θ : ℝ`,
`-√2 r sin θ - c r² (1 - cos θ) ≤ 1 / c`. -/
theorem neg_sqrt_two_mul_sin_sub_mul_one_sub_cos_le {c : ℝ} (hc : 0 < c) (r θ : ℝ) :
    -Real.sqrt 2 * r * Real.sin θ - c * r ^ 2 * (1 - Real.cos θ) ≤ 1 / c := by
  set s := Real.sin θ
  set k := 1 - Real.cos θ
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htrig : s ^ 2 + k ^ 2 = 2 * k := by
    have hpyth := Real.sin_sq_add_cos_sq θ
    dsimp [s, k]
    linear_combination hpyth
  have hdiff :
      2 * c * (1 / c - (-Real.sqrt 2 * r * s - c * r ^ 2 * k)) =
        (c * r * s + Real.sqrt 2) ^ 2 + c ^ 2 * r ^ 2 * k ^ 2 := by
    have hc_ne : c ≠ 0 := hc.ne'
    have h1 : 2 * c * (1 / c) = 2 := by field_simp [hc_ne]
    linear_combination h1 - (c ^ 2 * r ^ 2) * htrig - hs2
  have hnonneg :
      0 ≤ (c * r * s + Real.sqrt 2) ^ 2 + c ^ 2 * r ^ 2 * k ^ 2 := by positivity
  nlinarith

/-- **Exact Numerator SOS Upper Bound on `-(1 / 4 + r²) * I_2(r)`**:
for every `r : ℝ`,
`-(1 / 4 + r ^ 2) * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x ≤ 2 * (√2 - 1) * (1 / 4 + r ^ 2) + (16 + 19 * √2) / 12`. -/
theorem neg_mul_integral_one_two_cosLogProfile_le_linear_resolvent (r : ℝ) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
      2 * (Real.sqrt 2 - 1) * (1 / 4 + r ^ 2) + (16 + 19 * Real.sqrt 2) / 12 := by
  rw [neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r]
  set s2 := Real.sqrt 2
  set θ := r * Real.log 2
  set c := (4 - 2 * s2) / 3
  have hs2_low : (8119 / 5741 : ℝ) ≤ s2 := eight_thousand_one_hundred_nineteen_le_sqrt_two
  have hs2_high : s2 ≤ 577 / 408 := sqrt_two_le_five_seventy_seven_four_hundred_eighths
  have hs2_sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc_pos : 0 < c := by dsimp [c]; linarith
  have hc_inv : 1 / c = 3 * (2 + s2) / 4 := by
    have hc_ne : c ≠ 0 := hc_pos.ne'
    rw [div_eq_iff hc_ne]
    dsimp [c]
    linear_combination (1 / 2 : ℝ) * hs2_sq
  have hsos := neg_sqrt_two_mul_sin_sub_mul_one_sub_cos_le hc_pos r θ
  rw [hc_inv] at hsos
  have hcos_le : 1 - Real.cos θ ≤ 2 := by linarith [Real.neg_one_le_cos θ]
  have hcoeff_pos : 0 ≤ (2 * s2 - 1) / 3 := by linarith
  have hcos_term : ((2 * s2 - 1) / 3) * (1 - Real.cos θ) ≤ ((2 * s2 - 1) / 3) * 2 :=
    mul_le_mul_of_nonneg_left hcos_le hcoeff_pos
  have hrew :
      2 * (s2 - 1) * r ^ 2 - s2 * r * Real.sin θ +
        ((2 * s2 - 1) / 3 - ((4 - 2 * s2) / 3) * r ^ 2) * (1 - Real.cos θ) =
      2 * (s2 - 1) * (1 / 4 + r ^ 2) - (s2 - 1) / 2 +
        (-s2 * r * Real.sin θ - c * r ^ 2 * (1 - Real.cos θ)) +
        ((2 * s2 - 1) / 3) * (1 - Real.cos θ) := by
    dsimp [c]
    ring
  linarith

/-- **Global Exact Rational-Resolvent Lower Bound on `I_2(r)` (`Zero r² Growth`)**:
for every `r : ℝ`,
`-2 * (√2 - 1) - ((16 + 19 * √2) / 12) * (1 / (1 / 4 + r ^ 2)) ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x`. -/
theorem neg_two_sqrt_two_sub_one_sub_resolvent_le_integral_one_two_cosLogProfile (r : ℝ) :
    -2 * (Real.sqrt 2 - 1) - ((16 + 19 * Real.sqrt 2) / 12) * (1 / (1 / 4 + r ^ 2)) ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  have hden_pos : (0 : ℝ) < 1 / 4 + r ^ 2 := by positivity
  have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := hden_pos.ne'
  have hle := div_le_div_of_nonneg_right
    (neg_mul_integral_one_two_cosLogProfile_le_linear_resolvent r) hden_pos.le
  have hlhs :
      -(1 / 4 + r ^ 2) *
          (∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) /
          (1 / 4 + r ^ 2) =
        -∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
    field_simp [hden_ne]
  have hrhs :
      (2 * (Real.sqrt 2 - 1) * (1 / 4 + r ^ 2) + (16 + 19 * Real.sqrt 2) / 12) /
          (1 / 4 + r ^ 2) =
        2 * (Real.sqrt 2 - 1) + ((16 + 19 * Real.sqrt 2) / 12) * (1 / (1 / 4 + r ^ 2)) := by
    field_simp [hden_ne]
  rw [hlhs, hrhs] at hle
  linarith

/-- **Rational-Coefficient Resolvent Lower Bound on `I_2(r)`**:
for every `r : ℝ`,
`-(169 / 204) - (18 / 5) * (1 / (1 / 4 + r ^ 2)) ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x`. -/
theorem neg_rational_sub_resolvent_le_integral_one_two_cosLogProfile (r : ℝ) :
    -(169 / 204 : ℝ) - (18 / 5) * (1 / (1 / 4 + r ^ 2)) ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  have h := neg_two_sqrt_two_sub_one_sub_resolvent_le_integral_one_two_cosLogProfile r
  have hs2_high : Real.sqrt 2 ≤ 577 / 408 :=
    sqrt_two_le_five_seventy_seven_four_hundred_eighths
  have hinv_pos : 0 ≤ 1 / (1 / 4 + r ^ 2) := by positivity
  have hres_le :
      ((16 + 19 * Real.sqrt 2) / 12) * (1 / (1 / 4 + r ^ 2)) ≤
        (18 / 5) * (1 / (1 / 4 + r ^ 2)) := by
    refine mul_le_mul_of_nonneg_right ?_ hinv_pos
    linarith
  linarith

/-! ## Section 2: Global Uniform (`-91 / 100`) and Clamped Two-Regime (`-min ((7/480)r²) (91/100)`) First-Cell Bounds -/

/-- **Global Frequency-Uniform First-Cell Lower Bound (`-91 / 100 ≤ I_2(r)`)**:
for **every** `r : ℝ`, the first-cell quadrature kernel is bounded below by `-91 / 100 = -0.91`
(sharpening the crude triangle-inequality bound `-3` by more than a factor of `3.29` and removing
the `r²` divergence at high frequencies). -/
theorem neg_ninety_one_hundredths_le_integral_one_two_cosLogProfile (r : ℝ) :
    -(91 / 100 : ℝ) ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  rcases le_total (r ^ 2) 49 with hle | hge
  · have h := neg_seven_four_eightieths_mul_sq_le_integral_one_two_cosLogProfile r
    linarith
  · have h := neg_rational_sub_resolvent_le_integral_one_two_cosLogProfile r
    have hden : (197 / 4 : ℝ) ≤ 1 / 4 + r ^ 2 := by linarith
    have hinv : 1 / (1 / 4 + r ^ 2) ≤ 4 / 197 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

/-- **Global Clamped Two-Regime First-Cell Lower Bound**:
for **every** `r : ℝ`,
`-min ((7 / 480) * r ^ 2) (91 / 100) ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x`. -/
theorem neg_min_seven_four_eightieths_sq_ninety_one_hundredths_le_integral_one_two_cosLogProfile
    (r : ℝ) :
    -min ((7 / 480 : ℝ) * r ^ 2) (91 / 100) ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  have h1 := neg_seven_four_eightieths_mul_sq_le_integral_one_two_cosLogProfile r
  have h2 := neg_ninety_one_hundredths_le_integral_one_two_cosLogProfile r
  rcases min_cases ((7 / 480 : ℝ) * r ^ 2) (91 / 100) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> linarith

/-! ## Section 3: `S(f)`-Free and Clamped Spectral Integration on the First Cell `[1, 2]` -/

/-- Helper: integrability of the spectral first-cell integrand for any `f : WeilTestFn`. -/
theorem integrable_paperFT_norm_sq_mul_two_integral_one_two_cosLogProfile (f : WeilTestFn) :
    Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) := by
  have hmeas : AEStronglyMeasurable (fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)) volume := by
    have h1 : AEStronglyMeasurable (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2) volume :=
      (integrable_paperFT_norm_sq f).aestronglyMeasurable
    have h2 : Continuous fun r : ℝ =>
        ∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
      have hrew : (fun r : ℝ =>
          ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) =
          fun r : ℝ =>
            -(2 * (Real.sqrt 2 - 1) * r ^ 2 - Real.sqrt 2 * r * Real.sin (r * Real.log 2) +
              ((2 * Real.sqrt 2 - 1) / 3 - ((4 - 2 * Real.sqrt 2) / 3) * r ^ 2) *
                (1 - Real.cos (r * Real.log 2))) / (1 / 4 + r ^ 2) := by
        ext r
        have h := neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r
        have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hden_ne
        rw [mul_div_cancel₀ _ hden_ne]
        linarith
      rw [hrew]
      exact Continuous.div (by fun_prop) (by fun_prop) (fun _ => by positivity)
    exact h1.mul (continuous_const.mul h2).aestronglyMeasurable
  have hbound : ∀ r : ℝ,
      ‖‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)‖ ≤
        6 * ‖paperFT f.1 r‖ ^ 2 := by
    intro r
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hint_abs :
        |∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x| ≤ 3 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 1) (b := 2) (C := 3)
        (f := fun x => (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)
        (fun x hx => by
          rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
          have hx1 : 1 ≤ x := hx.1.le
          have hx2 : x ≤ 2 := hx.2
          have hsqrt_ge : 1 ≤ Real.sqrt x := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt hx1
          have hcos_abs : |cosLogProfile r x| ≤ 1 := Real.abs_cos_le_one _
          have hsec_abs : |cellSecant (cosLogProfile r) 2 x| ≤ 2 := by
            unfold cellSecant
            norm_num
            have ha : |cosLogProfile r 1| ≤ 1 := Real.abs_cos_le_one _
            have hb : |cosLogProfile r 2| ≤ 1 := Real.abs_cos_le_one _
            have htri := abs_add_le ((2 - x) * cosLogProfile r 1)
              ((x - 1) * cosLogProfile r 2)
            have hw1 : |2 - x| = 2 - x := abs_of_nonneg (by linarith)
            have hw2 : |x - 1| = x - 1 := abs_of_nonneg (by linarith)
            rw [abs_mul, abs_mul, hw1, hw2] at htri
            nlinarith
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hsqrt_ge)]
          refine (div_le_self (abs_nonneg _) hsqrt_ge).trans ?_
          have htri := abs_sub (cosLogProfile r x) (cellSecant (cosLogProfile r) 2 x)
          linarith)
      rw [Real.norm_eq_abs] at h
      linarith [show |(2 : ℝ) - 1| = 1 by norm_num]
    nlinarith [sq_nonneg ‖paperFT f.1 r‖]
  exact Integrable.mono' ((integrable_paperFT_norm_sq f).const_mul 6)
    hmeas (Eventually.of_forall hbound)

/-- **Exact `S(f)`-Free Rational-Resolvent First-Cell Quadrature Lower Bound**:
for **every** `f : WeilTestFn` (without any second-moment integrability assumption),
`-4 * (√2 - 1) * ∫ ‖f.1‖² - ((16 + 19 * √2) / 6) * bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤ ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / √x`. -/
theorem neg_four_sqrt_two_sub_one_l2_sub_resolvent_le_integral_one_two (f : WeilTestFn) :
    -4 * (Real.sqrt 2 - 1) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        ((16 + 19 * Real.sqrt 2) / 6) * bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤
      ∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x := by
  rw [integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f]
  have hsq := integrable_paperFT_norm_sq f
  have hres_int := integrable_paperFT_norm_sq_mul_inv_quarter_add_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hres_eq := bochnerResolventEnergy_weilTest_eq f
  let c1 := -2 * (Real.sqrt 2 - 1)
  let c2 := -((16 + 19 * Real.sqrt 2) / 6)
  have hlhs_eq :
      -4 * (Real.sqrt 2 - 1) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
          ((16 + 19 * Real.sqrt 2) / 6) * bochnerResolventEnergy (EF.weilTest f.1 f.1) =
        (1 / (2 * Real.pi)) *
          ∫ r : ℝ,
            (c1 * (‖paperFT f.1 r‖ ^ 2 * 2) +
              c2 * (‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)))) := by
    rw [hres_eq,
      integral_add ((hsq.mul_const 2).const_mul c1) (hres_int.const_mul c2),
      integral_const_mul, integral_const_mul]
    dsimp [c1, c2]
    linear_combination 2 * (Real.sqrt 2 - 1) * hplanch
  rw [hlhs_eq]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono
    (((hsq.mul_const 2).const_mul c1).add (hres_int.const_mul c2))
    (integrable_paperFT_norm_sq_mul_two_integral_one_two_cosLogProfile f) fun r => ?_
  dsimp only [c1, c2]
  have hpt := neg_two_sqrt_two_sub_one_sub_resolvent_le_integral_one_two_cosLogProfile r
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpt (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖paperFT f.1 r‖)
  linarith

/-- **Rational-Coefficient `S(f)`-Free Resolvent First-Cell Quadrature Lower Bound**:
for **every** `f : WeilTestFn`,
`-(169 / 102) * ∫ ‖f.1‖² - (36 / 5) * bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤ ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / √x`. -/
theorem neg_rational_l2_sub_resolvent_le_integral_one_two (f : WeilTestFn) :
    -(169 / 102 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (36 / 5) * bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤
      ∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x := by
  have h := neg_four_sqrt_two_sub_one_l2_sub_resolvent_le_integral_one_two f
  have hs2_high : Real.sqrt 2 ≤ 577 / 408 :=
    sqrt_two_le_five_seventy_seven_four_hundred_eighths
  have hL_nn : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres_nn : 0 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) :=
    bochnerResolventEnergy_weilTest_nonneg f
  have h1 : 4 * (Real.sqrt 2 - 1) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      (169 / 102) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hL_nn
  have h2 : ((16 + 19 * Real.sqrt 2) / 6) * bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤
      (36 / 5) * bochnerResolventEnergy (EF.weilTest f.1 f.1) :=
    mul_le_mul_of_nonneg_right (by linarith) hres_nn
  linarith

/-- **Uniform `S(f)`-Free First-Cell Quadrature Lower Bound (`-(91 / 50) * ∫ ‖f.1‖²`)**:
for **every** `f : WeilTestFn`,
`-(91 / 50) * ∫ ‖f.1‖² ≤ ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / √x`. -/
theorem neg_ninety_one_fiftieths_l2_le_integral_one_two (f : WeilTestFn) :
    -(91 / 50 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x := by
  rw [integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f]
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hlhs_eq :
      -(91 / 50 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
        (1 / (2 * Real.pi)) * ∫ r : ℝ, -(91 / 100 : ℝ) * (‖paperFT f.1 r‖ ^ 2 * 2) := by
    rw [integral_const_mul]
    linear_combination (91 / 100 : ℝ) * hplanch
  rw [hlhs_eq]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono
    ((hsq.mul_const 2).const_mul (-(91 / 100 : ℝ)))
    (integrable_paperFT_norm_sq_mul_two_integral_one_two_cosLogProfile f) fun r => ?_
  dsimp only
  have hpt := neg_ninety_one_hundredths_le_integral_one_two_cosLogProfile r
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hpt (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg ‖paperFT f.1 r‖)
  linarith

/-- **Clamped Two-Regime Spectral First-Cell Quadrature Lower Bound**:
for every `f : WeilTestFn` with integrable second spectral moment,
`-min ((7 / 480) * spectralSecondMoment f.1) ((91 / 50) * ∫ ‖f.1‖²) ≤ ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / √x`. -/
theorem neg_min_first_cell_le_integral_one_two
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    -min ((7 / 480 : ℝ) * spectralSecondMoment f.1)
        ((91 / 50) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x := by
  have h1 := neg_seven_four_eightieths_spectralSecondMoment_le_integral_one_two f hint2
  have h2 := neg_ninety_one_fiftieths_l2_le_integral_one_two f
  rcases min_cases ((7 / 480 : ℝ) * spectralSecondMoment f.1)
    ((91 / 50) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> linarith

/-- **Clamped Secant Numerator Cell Defect Bound (`secantNumeratorCellDefect`)**:
replacing the unbounded `(7 / 480) * S` first-cell contribution by the clamped minimum
`min ((7 / 480) * S) ((91 / 50) * L)` bounds `secantNumeratorCellDefect f.1 N` from below across
all ratios `S / L`. -/
theorem neg_clamped_first_cell_sub_seventy_one_geom_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -min ((7 / 480 : ℝ) * spectralSecondMoment f.1)
          ((91 / 50) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment f.1 *
              (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      secantNumeratorCellDefect f.1 N := by
  have hS_nn : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nn : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  unfold secantNumeratorCellDefect
  by_cases hN : 2 ≤ N
  · rw [sum_Icc_two_eq_add_sum_Icc_three _ hN]
    have h2 := neg_min_first_cell_le_integral_one_two f hint2
    have h3 := neg_seventy_one_thirty_six_hundredths_sqrt_le_sum_Icc_three f hint2 N
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    have hmin_nn :
        0 ≤ min ((7 / 480 : ℝ) * spectralSecondMoment f.1)
          ((91 / 50) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :=
      le_min (by positivity) (by positivity)
    have hsqrt_nn : 0 ≤ Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) := Real.sqrt_nonneg _
    linarith

/-! ## Section 4: `S(F)`-Free Tail-Cell (`n ≥ 3`) Variance Localization and Clamped All-Ratio Laws -/

/-- **`S(f)`-Free Origin + First-Cell Resolvent Lower Bound**:
for every `f : WeilTestFn`, the sum of the origin boundary term `((16√2 - 20)/3) ∫ ‖f.1‖²` and the
first-cell quadrature integral `∫_1^2 ...` is bounded below purely by `-(79 / 100) ∫ ‖f.1‖² - (36 / 5) * bochnerResolventEnergy k_f`,
with **no `spectralSecondMoment` term**. -/
theorem neg_seventy_nine_hundredths_l2_sub_resolvent_le_origin_add_first_cell (f : WeilTestFn) :
    -(79 / 100 : ℝ) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        (36 / 5) * bochnerResolventEnergy (EF.weilTest f.1 f.1) ≤
      ((16 * Real.sqrt 2 - 20) / 3) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        ∫ x in (1 : ℝ)..2,
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
            Real.sqrt x := by
  have h1 := neg_rational_l2_sub_resolvent_le_integral_one_two f
  have hs2_low : (8119 / 5741 : ℝ) ≤ Real.sqrt 2 :=
    eight_thousand_one_hundred_nineteen_le_sqrt_two
  have hL_nn : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcoeff : -(79 / 100 : ℝ) ≤ (16 * Real.sqrt 2 - 20) / 3 - 169 / 102 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hL_nn
  linarith

/-- **Tail-Cell (`n ≥ 3`) Variance Localization on the Prime-Blind Primitive Cone (`Zero S(F) Dependence`)**:
for every prime-blind `f ∈ C²_c(ℝ)` (`logVector F = 0`) with `coshHalfMoment f = 0` and support
cutoff `2 ≤ N`, eliminating `spectralSecondMoment F` on the first cell `n = 2` localizes the
high-frequency defect onto the tail cells `n ∈ Finset.Icc 3 N`:
`2 * sinhHalfMoment f ^ 2 + ∑ n ∈ Finset.Icc 3 N, ∫ x in (n-1)..n, (C_F x - cellSecant C_F n x) / √x ≤ (79 / 100) * ∫ ‖F‖² + (31 / 5) * bochnerResolventEnergy k_F`. -/
theorem tail_cell_variance_localization_of_cosh_zero_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    {N : ℕ} (hN2 : 2 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0) :
    2 * sinhHalfMoment f ^ 2 +
        (∑ n ∈ Finset.Icc 3 N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator (realWeilTestFn f hf hfc).1 x -
              cellSecant (weilSymmetricLogNumerator (realWeilTestFn f hf hfc).1) n x) /
              Real.sqrt x) ≤
      (79 / 100 : ℝ) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (31 / 5) *
          bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) := by
  let F := realWeilTestFn f hf hfc
  have hN1 : 1 ≤ N := by omega
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hunit_zero : primeBlindCounterterm unitStepCountertermWeight F = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hcomb_zero : primeBlindCounterterm secantCombinedSecularWeight F = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hdecomp :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      F hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  rw [hcomb_zero, add_zero] at hdecomp
  unfold secantNumeratorCellDefect at hdecomp
  rw [sum_Icc_two_eq_add_sum_Icc_three _ hN2] at hdecomp
  have hcell1 := neg_seventy_nine_hundredths_l2_sub_resolvent_le_origin_add_first_cell F
  linarith

/-- **Clamped All-Ratio Conservation Inequality on the Primitive Hyperplane (`coshHalfMoment f = 0`)**:
replacing `(7 / 480) * S` on the first cell by the clamped minimum
`min ((7 / 480) * S) ((91 / 50) * L)` sharpens `all_ratio_conservation_bound_of_cosh_zero` at all
high ratios `S / L > 124.8`. -/
theorem clamped_all_ratio_conservation_bound_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    (247 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 +
        primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) ≤
      min ((7 / 480 : ℝ) * spectralSecondMoment (realWeilTestFn f hf hfc).1)
          ((91 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) := by
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_clamped_first_cell_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  linarith

/-- **Clamped All-Ratio `markovEnergy ≥ (1 / 100) * ∫ ‖F‖² ≥ 0` Closure on the Primitive Hyperplane**:
whenever `2 * sinhHalfMoment f ^ 2` covers the clamped high-frequency excess
`min ((7 / 480) * S) ((91 / 50) * L) + (71 / 3600) * √(S(S + 2L)) - (41 / 50) * L`, we have
`(1 / 100) * ∫ ‖F‖² ≤ markovEnergy F` and `0 ≤ markovEnergy F`. -/
theorem clamped_all_ratio_markovEnergy_nonneg_of_sinh_sq_dominates
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hdom :
      min ((7 / 480 : ℝ) * spectralSecondMoment (realWeilTestFn f hf hfc).1)
            ((91 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          (71 / 3600) *
            Real.sqrt
              (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
                (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
                  2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (41 / 50) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
          2 * sinhHalfMoment f ^ 2) :
    (1 / 100) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        markovEnergy (realWeilTestFn f hf hfc).1 ∧
      0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 600
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (600 : ℝ) ≤ θ := le_max_right _ _
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_clamped_first_cell_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hquad_sinh :
      (1 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
          2 * sinhHalfMoment f ^ 2 := by
    linarith
  have hθ_mul :
      (600 : ℝ) * ((1 / 300) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        θ *
          (rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N +
            2 * sinhHalfMoment f ^ 2) :=
    mul_le_mul hθ_large hquad_sinh (by positivity) (by linarith)
  have hres_nn :
      0 ≤ (θ - 1) * bochnerResolventEnergy
        (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc))
  refine ⟨by linarith, by linarith⟩

end RHTower
