import Mathlib

/-!
# Nonnegative generalized von Mangoldt measure plus the Riemann functional equation
does not force the critical line

Write a generalized Euler system in logarithmic coordinates: a nonnegative measure `dΨ` on
`[0,∞)` with

```text
M(s) = ∫_0^∞ e^{-s u} dΨ(u)        (= ∫_1^∞ x^{-s} dψ(x),  x = e^u),
```

so that `M` is the logarithmic derivative `-F'/F` of the associated system.  Nonnegativity of
`dΨ` is exactly `Λ ≥ 0`.  The completed function `π^{-s/2}Γ(s/2)F(s)` obeys the Riemann functional
equation precisely when

```text
M(s) + M(1-s) = (1/2)[Ψ_dig(s/2) + Ψ_dig((1-s)/2)] - log π,
```

whose right-hand side is a fixed archimedean kernel.  Hence the difference of any two solutions is
a *reflection-antisymmetric* transform `N(s) = -N(1-s)`.

This module exhibits an explicit **nonnegative** reflection-antisymmetric density whose transform
has residue `-1` at a prescribed off-critical quadruple `ρ, ρ̄, 1-ρ, 1-ρ̄` with `Re ρ ∈ (1/2,1)`.
Adding it to the von Mangoldt measure keeps `Λ ≥ 0` and keeps the functional equation, while
creating four zeros off the critical line.  Its rational gauge

```text
G(s) = (s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄) / [(s-1/2-c)(s-1/2+c)]^4
```

is reflection invariant, so `F = ζ·G` has the same completed functional equation as `ζ`.

Consequence: `Λ ≥ 0` together with the Riemann functional equation is *not* sufficient to place
zeros on the critical line.  The positive dominating part of the correction is forced (it is what
makes the density nonnegative), and it contributes poles at `1/2 ± c`.  So the missing third input
is the **holomorphy of the completed function inside the strip**, not any further property of the
source.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-! ## Laplace transform of a damped cosine -/

/-- `∫_0^∞ e^{-a u} cos(b u) du = a/(a²+b²)` for `a > 0`. -/
theorem integral_Ioi_exp_neg_mul_cos {a b : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(a * u)) * Real.cos (b * u)) = a / (a ^ 2 + b ^ 2) := by
  have hden : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  set F : ℝ → ℝ := fun u =>
    Real.exp (-(a * u)) * (b * Real.sin (b * u) - a * Real.cos (b * u)) / (a ^ 2 + b ^ 2) with hF
  have hderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivAt F (Real.exp (-(a * u)) * Real.cos (b * u)) u := by
    intro u _
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(a * u))) (Real.exp (-(a * u)) * (-a)) u := by
      have h : HasDerivAt (fun u : ℝ => -(a * u)) (-a) u := by
        have hraw := ((hasDerivAt_id u).const_mul a).neg
        have hfun :
            -(fun y : ℝ => a * id y) = (fun y : ℝ => -(a * y)) := by
          funext y
          rfl
        rw [hfun] at hraw
        apply hraw.congr_deriv
        ring
      simpa using h.exp
    have hsin : HasDerivAt (fun u : ℝ => Real.sin (b * u)) (Real.cos (b * u) * b) u := by
      simpa using ((hasDerivAt_id u).const_mul b).sin
    have hcos : HasDerivAt (fun u : ℝ => Real.cos (b * u)) (-Real.sin (b * u) * b) u := by
      simpa using ((hasDerivAt_id u).const_mul b).cos
    have hmix : HasDerivAt (fun u : ℝ => b * Real.sin (b * u) - a * Real.cos (b * u))
        (b * (Real.cos (b * u) * b) - a * (-Real.sin (b * u) * b)) u :=
      (hsin.const_mul b).sub (hcos.const_mul a)
    have hprod := (hexp.mul hmix).div_const (a ^ 2 + b ^ 2)
    rw [hF]
    apply hprod.congr_deriv
    field_simp [hden.ne']
    ring
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have : Continuous F := by rw [hF]; fun_prop
    exact this.continuousWithinAt
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-(a * u)) * Real.cos (b * u)) (Ioi 0) := by
    have hdom : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 ha
    apply MeasureTheory.Integrable.mono' hdom
    · exact ((Real.continuous_exp.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hcos : |Real.cos (b * u)| ≤ 1 := Real.abs_cos_le_one _
      have h1 : Real.exp (-(a * u)) * |Real.cos (b * u)| ≤ Real.exp (-(a * u)) * 1 :=
        mul_le_mul_of_nonneg_left hcos (le_of_lt (Real.exp_pos _))
      have h2 : Real.exp (-(a * u)) = |Real.exp (-a * u)| := by
        rw [abs_of_pos (Real.exp_pos _)]; ring_nf
      rw [h2] at h1 ⊢
      simpa using h1
  have htop : Tendsto F atTop (𝓝 0) := by
    have hbound : ∀ u : ℝ, |F u| ≤ Real.exp (-(a * u)) * ((|b| + |a|) / (a ^ 2 + b ^ 2)) := by
      intro u
      rw [hF]
      simp only [abs_div, abs_mul]
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos hden]
      have hnum : |b * Real.sin (b * u) - a * Real.cos (b * u)| ≤ |b| + |a| := by
        refine (abs_sub _ _).trans ?_
        have h1 : |b * Real.sin (b * u)| ≤ |b| := by
          rw [abs_mul]
          calc |b| * |Real.sin (b * u)| ≤ |b| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg b)
            _ = |b| := mul_one _
        have h2 : |a * Real.cos (b * u)| ≤ |a| := by
          rw [abs_mul]
          calc |a| * |Real.cos (b * u)| ≤ |a| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg a)
            _ = |a| := mul_one _
        linarith
      rw [div_le_iff₀ hden, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hden)]
      exact mul_le_mul_of_nonneg_left hnum (le_of_lt (Real.exp_pos _))
    have hexp0 : Tendsto (fun u : ℝ => Real.exp (-(a * u)) * ((|b| + |a|) / (a ^ 2 + b ^ 2)))
        atTop (𝓝 0) := by
      have hlin : Tendsto (fun u : ℝ => -(a * u)) atTop atBot := by
        have h0 : Tendsto (fun u : ℝ => a * u) atTop atTop :=
          Filter.Tendsto.const_mul_atTop ha tendsto_id
        exact tendsto_neg_atTop_atBot.comp h0
      have h : Tendsto (fun u : ℝ => Real.exp (-(a * u))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hlin
      simpa using h.mul_const ((|b| + |a|) / (a ^ 2 + b ^ 2))
    exact squeeze_zero_norm (fun u => by simpa [Real.norm_eq_abs] using hbound u) hexp0
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  rw [hmain, hF]
  simp
  field_simp

/-- `∫_0^∞ e^{-a u} du = 1/a` for `a > 0`, as the `b = 0` case. -/
theorem integral_Ioi_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(a * u))) = 1 / a := by
  have h := integral_Ioi_exp_neg_mul_cos (a := a) (b := 0) ha
  simp only [zero_mul, Real.cos_zero, mul_one] at h
  rw [h]
  have : a ^ 2 + (0 : ℝ) ^ 2 = a * a := by ring
  rw [this]
  field_simp

/-! ## The nonnegative reflection-antisymmetric density -/

/-- Logarithmic density of the reflection-antisymmetric correction.  Its four oscillating terms
supply the off-critical quadruple; the two leading terms are the positive dominating part forced by
nonnegativity. -/
def feNeutralLogDensity (beta gam c : ℝ) (u : ℝ) : ℝ :=
  4 * (Real.exp ((c + 1 / 2) * u) + Real.exp ((1 / 2 - c) * u)) -
    2 * Real.cos (gam * u) * (Real.exp (beta * u) + Real.exp ((1 - beta) * u))

/-- **The correction is a nonnegative measure**, i.e. it preserves `Λ ≥ 0`. -/
theorem feNeutralLogDensity_nonneg {beta gam c u : ℝ}
    (hb0 : 1 / 2 < beta) (hc0 : beta - 1 / 2 < c) (hu : 0 ≤ u) :
    0 ≤ feNeutralLogDensity beta gam c u := by
  have hdom1 : Real.exp (beta * u) ≤ Real.exp ((c + 1 / 2) * u) := by
    apply Real.exp_le_exp.mpr
    have : beta ≤ c + 1 / 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hu
  have hdom2 : Real.exp ((1 - beta) * u) ≤ Real.exp ((c + 1 / 2) * u) := by
    apply Real.exp_le_exp.mpr
    have hc : 0 < c := by linarith
    have : 1 - beta ≤ c + 1 / 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hu
  have hcos : Real.cos (gam * u) ≤ 1 := Real.cos_le_one _
  have hpos : 0 < Real.exp (beta * u) + Real.exp ((1 - beta) * u) := by positivity
  have hstep : 2 * Real.cos (gam * u) * (Real.exp (beta * u) + Real.exp ((1 - beta) * u))
      ≤ 2 * (Real.exp (beta * u) + Real.exp ((1 - beta) * u)) := by
    nlinarith [hpos, hcos]
  have hpos2 : (0 : ℝ) < Real.exp ((1 / 2 - c) * u) := Real.exp_pos _
  rw [feNeutralLogDensity]
  nlinarith [hdom1, hdom2, hstep, hpos2]

/-! ## Its Laplace transform -/

/-- Real form of the transform of the correction. -/
def feNeutralTransformReal (beta gam c : ℝ) (σ : ℝ) : ℝ :=
  4 * (1 / (σ - c - 1 / 2) + 1 / (σ - 1 / 2 + c)) -
    2 * ((σ - beta) / ((σ - beta) ^ 2 + gam ^ 2) +
      (σ - 1 + beta) / ((σ - 1 + beta) ^ 2 + gam ^ 2))

/-- **The transform of the nonnegative correction.**  Valid on the half plane of absolute
convergence `σ > c + 1/2`, which contains `σ > 1` because `c < 1/2`. -/
theorem integral_feNeutralLogDensity {beta gam c σ : ℝ}
    (hb0 : 1 / 2 < beta) (hc0 : beta - 1 / 2 < c) (hσ : c + 1 / 2 < σ) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * feNeutralLogDensity beta gam c u) =
      feNeutralTransformReal beta gam c σ := by
  have hc : 0 < c := by linarith
  have h1 : (0 : ℝ) < σ - c - 1 / 2 := by linarith
  have h2 : (0 : ℝ) < σ - 1 / 2 + c := by linarith
  have h3 : (0 : ℝ) < σ - beta := by linarith
  have h4 : (0 : ℝ) < σ - 1 + beta := by linarith
  have key : ∀ p : ℝ, 0 < σ - p →
      (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * Real.exp (p * u)) = 1 / (σ - p) := by
    intro p hp
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp (p * u))
        = fun u : ℝ => Real.exp (-((σ - p) * u)) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr, integral_Ioi_exp_neg_mul hp]
  have keycos : ∀ p : ℝ, 0 < σ - p →
      (∫ u in Ioi (0 : ℝ),
          Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u)))
        = (σ - p) / ((σ - p) ^ 2 + gam ^ 2) := by
    intro p hp
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u)))
        = fun u : ℝ => Real.exp (-((σ - p) * u)) * Real.cos (gam * u) := by
      funext u
      rw [show Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u))
          = (Real.exp (-(σ * u)) * Real.exp (p * u)) * Real.cos (gam * u) from by ring,
        ← Real.exp_add]
      congr 2
      ring
    rw [hcongr, integral_Ioi_exp_neg_mul_cos hp]
  have hsplit : (fun u : ℝ => Real.exp (-(σ * u)) * feNeutralLogDensity beta gam c u)
      = fun u : ℝ =>
        4 * (Real.exp (-(σ * u)) * Real.exp ((c + 1 / 2) * u)) +
          4 * (Real.exp (-(σ * u)) * Real.exp ((1 / 2 - c) * u)) -
          (2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (beta * u))) +
            2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp ((1 - beta) * u)))) := by
    funext u; rw [feNeutralLogDensity]; ring
  have hi1 : IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((c + 1 / 2) * u))
      (Ioi 0) := by
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((c + 1 / 2) * u))
        = fun u : ℝ => Real.exp (-(σ - (c + 1 / 2)) * u) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]; exact exp_neg_integrableOn_Ioi 0 (by linarith)
  have hi2 : IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((1 / 2 - c) * u))
      (Ioi 0) := by
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((1 / 2 - c) * u))
        = fun u : ℝ => Real.exp (-(σ - (1 / 2 - c)) * u) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]; exact exp_neg_integrableOn_Ioi 0 (by linarith)
  have hbound : ∀ p : ℝ, 0 < σ - p →
      IntegrableOn (fun u : ℝ =>
        Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u))) (Ioi 0) := by
    intro p hp
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u)))
        = fun u : ℝ => Real.exp (-((σ - p) * u)) * Real.cos (gam * u) := by
      funext u
      rw [show Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u))
          = (Real.exp (-(σ * u)) * Real.exp (p * u)) * Real.cos (gam * u) from by ring,
        ← Real.exp_add]
      congr 2
      ring
    rw [hcongr]
    apply MeasureTheory.Integrable.mono' (exp_neg_integrableOn_Ioi 0 hp)
    · exact ((Real.continuous_exp.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hcos : |Real.cos (gam * u)| ≤ 1 := Real.abs_cos_le_one _
      have h1' : Real.exp (-((σ - p) * u)) * |Real.cos (gam * u)| ≤ Real.exp (-((σ - p) * u)) * 1 :=
        mul_le_mul_of_nonneg_left hcos (le_of_lt (Real.exp_pos _))
      have h2' : Real.exp (-((σ - p) * u)) = |Real.exp (-(σ - p) * u)| := by
        rw [abs_of_pos (Real.exp_pos _)]; ring_nf
      rw [h2'] at h1' ⊢
      simpa using h1'
  have I1 : IntegrableOn
      (fun u : ℝ => 4 * (Real.exp (-(σ * u)) * Real.exp ((c + 1 / 2) * u))) (Ioi 0) :=
    hi1.const_mul 4
  have I2 : IntegrableOn
      (fun u : ℝ => 4 * (Real.exp (-(σ * u)) * Real.exp ((1 / 2 - c) * u))) (Ioi 0) :=
    hi2.const_mul 4
  have I3 : IntegrableOn
      (fun u : ℝ => 2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (beta * u))))
      (Ioi 0) := (hbound beta h3).const_mul 2
  have I4 : IntegrableOn
      (fun u : ℝ =>
        2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp ((1 - beta) * u)))) (Ioi 0) :=
    (hbound (1 - beta) (by linarith)).const_mul 2
  have hA := I1.add I2
  have hAfun :
      ((fun u : ℝ => 4 * (Real.exp (-(σ * u)) * Real.exp ((c + 1 / 2) * u))) +
        fun u : ℝ => 4 * (Real.exp (-(σ * u)) * Real.exp ((1 / 2 - c) * u))) =
        (fun u : ℝ => 4 * (Real.exp (-(σ * u)) * Real.exp ((c + 1 / 2) * u)) +
          4 * (Real.exp (-(σ * u)) * Real.exp ((1 / 2 - c) * u))) := by
    funext u
    rfl
  rw [hAfun] at hA
  have hB := I3.add I4
  have hBfun :
      ((fun u : ℝ =>
          2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (beta * u)))) +
        fun u : ℝ =>
          2 * (Real.exp (-(σ * u)) *
            (Real.cos (gam * u) * Real.exp ((1 - beta) * u)))) =
        (fun u : ℝ =>
          2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (beta * u))) +
          2 * (Real.exp (-(σ * u)) *
            (Real.cos (gam * u) * Real.exp ((1 - beta) * u)))) := by
    funext u
    rfl
  rw [hBfun] at hB
  rw [hsplit, integral_sub hA hB, integral_add I1 I2, integral_add I3 I4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [key _ (by linarith), key _ (by linarith), keycos _ h3, keycos _ (by linarith)]
  rw [feNeutralTransformReal]
  have e1 : σ - (c + 1 / 2) = σ - c - 1 / 2 := by ring
  have e2 : σ - (1 / 2 - c) = σ - 1 / 2 + c := by ring
  have e3 : σ - (1 - beta) = σ - 1 + beta := by ring
  rw [e1, e2, e3]
  ring

/-! ## Reflection antisymmetry of the transform -/

/-- Complex form of the transform of the correction. -/
def feNeutralTransform (beta gam c : ℝ) (s : ℂ) : ℂ :=
  4 * ((s - ((1 : ℂ) / 2 + c))⁻¹ + (s - ((1 : ℂ) / 2 - c))⁻¹) -
    ((s - ((beta : ℂ) + (gam : ℂ) * I))⁻¹ + (s - ((beta : ℂ) - (gam : ℂ) * I))⁻¹ +
      (s - (1 - ((beta : ℂ) + (gam : ℂ) * I)))⁻¹ + (s - (1 - ((beta : ℂ) - (gam : ℂ) * I)))⁻¹)

/-- **Reflection antisymmetry.**  The transform is exactly the difference of two solutions of the
Riemann reflection identity, so adding it preserves the functional equation.  The identity holds
with no side conditions: reciprocal junk values cancel in the same pattern. -/
theorem feNeutralTransform_antisymm (beta gam c : ℝ) (s : ℂ) :
    feNeutralTransform beta gam c s + feNeutralTransform beta gam c (1 - s) = 0 := by
  have pair : ∀ r : ℂ, (s - r)⁻¹ + (s - (1 - r))⁻¹ +
      ((1 - s - r)⁻¹ + (1 - s - (1 - r))⁻¹) = 0 := by
    intro r
    have h1 : (1 : ℂ) - s - r = -(s - (1 - r)) := by ring
    have h2 : (1 : ℂ) - s - (1 - r) = -(s - r) := by ring
    rw [h1, h2, inv_neg, inv_neg]
    ring
  simp only [feNeutralTransform]
  have hb : (1 : ℂ) - ((beta : ℂ) + (gam : ℂ) * I) = 1 - ((beta : ℂ) + (gam : ℂ) * I) := rfl
  have hkey1 := pair ((1 : ℂ) / 2 + c)
  have hkey2 := pair ((beta : ℂ) + (gam : ℂ) * I)
  have hkey3 := pair ((beta : ℂ) - (gam : ℂ) * I)
  have hhalf : (1 : ℂ) - ((1 : ℂ) / 2 + c) = (1 : ℂ) / 2 - c := by ring
  rw [hhalf] at hkey1
  have hrev1 : (1 : ℂ) - (1 - ((beta : ℂ) + (gam : ℂ) * I)) = (beta : ℂ) + (gam : ℂ) * I := by ring
  have hrev2 : (1 : ℂ) - (1 - ((beta : ℂ) - (gam : ℂ) * I)) = (beta : ℂ) - (gam : ℂ) * I := by ring
  linear_combination (4 : ℂ) * hkey1 - hkey2 - hkey3

/-- Conjugate pair of Cauchy kernels at a real point. -/
theorem inv_add_inv_conjugate_pair {x y : ℝ} (h : 0 < x ^ 2 + y ^ 2) :
    (((x : ℂ) - (y : ℂ) * I)⁻¹ + ((x : ℂ) + (y : ℂ) * I)⁻¹)
      = ((2 * x / (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  have hprod : ((x : ℂ) - (y : ℂ) * I) * ((x : ℂ) + (y : ℂ) * I) = ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [show ((x : ℂ) - (y : ℂ) * I) * ((x : ℂ) + (y : ℂ) * I)
        = (x : ℂ) ^ 2 - (y : ℂ) ^ 2 * I ^ 2 from by ring, Complex.I_sq]
    ring
  have hnz : ((x ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h)
  have ha : ((x : ℂ) - (y : ℂ) * I) ≠ 0 := by
    intro hc
    apply hnz
    rw [← hprod, hc, zero_mul]
  have hb : ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro hc
    apply hnz
    rw [← hprod, hc, mul_zero]
  rw [inv_add_inv ha hb, hprod]
  rw [show ((x : ℂ) - (y : ℂ) * I) + ((x : ℂ) + (y : ℂ) * I) = ((2 * x : ℝ) : ℂ) from by
    push_cast; ring]
  rw [← Complex.ofReal_div]

/-- The complex transform restricted to the real axis is the real transform. -/
theorem feNeutralTransform_ofReal {beta gam c σ : ℝ}
    (hb0 : 1 / 2 < beta) (hc0 : beta - 1 / 2 < c) (hσ : c + 1 / 2 < σ) :
    feNeutralTransform beta gam c (σ : ℂ) = ((feNeutralTransformReal beta gam c σ : ℝ) : ℂ) := by
  have hc : 0 < c := by linarith
  have h1 : (0 : ℝ) < σ - c - 1 / 2 := by linarith
  have h2 : (0 : ℝ) < σ - 1 / 2 + c := by linarith
  have h3 : (0 : ℝ) < σ - beta := by linarith
  have h4 : (0 : ℝ) < σ - 1 + beta := by linarith
  have hq3 : (0 : ℝ) < (σ - beta) ^ 2 + gam ^ 2 := by positivity
  have hq4 : (0 : ℝ) < (σ - 1 + beta) ^ 2 + gam ^ 2 := by positivity
  have e1 : (σ : ℂ) - ((1 : ℂ) / 2 + c) = ((σ - c - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (σ : ℂ) - ((1 : ℂ) / 2 - c) = ((σ - 1 / 2 + c : ℝ) : ℂ) := by push_cast; ring
  have e3 : (σ : ℂ) - ((beta : ℂ) + (gam : ℂ) * I)
      = ((σ - beta : ℝ) : ℂ) - ((gam : ℝ) : ℂ) * I := by push_cast; ring
  have e4 : (σ : ℂ) - ((beta : ℂ) - (gam : ℂ) * I)
      = ((σ - beta : ℝ) : ℂ) + ((gam : ℝ) : ℂ) * I := by push_cast; ring
  have e5 : (σ : ℂ) - (1 - ((beta : ℂ) - (gam : ℂ) * I))
      = ((σ - 1 + beta : ℝ) : ℂ) - ((gam : ℝ) : ℂ) * I := by push_cast; ring
  have e6 : (σ : ℂ) - (1 - ((beta : ℂ) + (gam : ℂ) * I))
      = ((σ - 1 + beta : ℝ) : ℂ) + ((gam : ℝ) : ℂ) * I := by push_cast; ring
  rw [feNeutralTransform, e1, e2]
  rw [show ((σ : ℂ) - ((beta : ℂ) + (gam : ℂ) * I))⁻¹ + ((σ : ℂ) - ((beta : ℂ) - (gam : ℂ) * I))⁻¹
      + ((σ : ℂ) - (1 - ((beta : ℂ) + (gam : ℂ) * I)))⁻¹
      + ((σ : ℂ) - (1 - ((beta : ℂ) - (gam : ℂ) * I)))⁻¹
      = (((σ : ℂ) - ((beta : ℂ) + (gam : ℂ) * I))⁻¹
          + ((σ : ℂ) - ((beta : ℂ) - (gam : ℂ) * I))⁻¹)
        + (((σ : ℂ) - (1 - ((beta : ℂ) - (gam : ℂ) * I)))⁻¹
          + ((σ : ℂ) - (1 - ((beta : ℂ) + (gam : ℂ) * I)))⁻¹) from by ring]
  rw [e3, e4, e5, e6]
  rw [inv_add_inv_conjugate_pair hq3, inv_add_inv_conjugate_pair hq4]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_inv]
  rw [feNeutralTransformReal]
  push_cast
  rw [one_div, one_div]
  ring

/-! ## The reflection-invariant rational gauge -/

/-- The rational gauge whose logarithmic derivative is the correction transform. -/
def feGauge (beta gam c : ℝ) (s : ℂ) : ℂ :=
  ((s - ((beta : ℂ) + (gam : ℂ) * I)) * (s - ((beta : ℂ) - (gam : ℂ) * I)) *
      (s - (1 - ((beta : ℂ) + (gam : ℂ) * I))) * (s - (1 - ((beta : ℂ) - (gam : ℂ) * I)))) /
    ((s - ((1 : ℂ) / 2 + c)) * (s - ((1 : ℂ) / 2 - c))) ^ 4

/-- **The gauge is invariant under `s ↦ 1-s`.**  Hence `π^{-s/2}Γ(s/2)·ζ(s)·G(s)` obeys exactly the
Riemann functional equation. -/
theorem feGauge_reflect (beta gam c : ℝ) (s : ℂ) :
    feGauge beta gam c (1 - s) = feGauge beta gam c s := by
  unfold feGauge
  congr 1
  · ring
  · ring

/-- **The gauge vanishes at the prescribed off-critical node.** -/
theorem feGauge_eq_zero (beta gam c : ℝ) :
    feGauge beta gam c ((beta : ℂ) + (gam : ℂ) * I) = 0 := by
  unfold feGauge
  simp

/-! ## The packaged statement -/

/-- **`Λ ≥ 0` plus the Riemann functional equation does not force the critical line.**

For every prescribed off-critical abscissa `β ∈ (1/2,1)`, ordinate `γ`, and every
`c ∈ (β-1/2, 1/2)`:

* the logarithmic correction density is nonnegative on `[0,∞)`, so adding it to the von Mangoldt
  measure preserves nonnegativity of the generalized von Mangoldt measure;
* its Laplace transform is absolutely convergent on `σ > c + 1/2`, a half plane containing
  `σ > 1`;
* that transform is exactly reflection antisymmetric, so the completed function of the perturbed
  system satisfies the *same* functional equation as `ζ`;
* the associated rational gauge is reflection invariant and vanishes at `β + iγ`, so the perturbed
  system has zeros off the critical line.

The positive dominating part of the density is forced by nonnegativity and contributes the poles
at `1/2 ± c`.  Thus the third input needed for a critical-line theorem is holomorphy of the
completed function inside the strip, not any further property of the arithmetic source. -/
theorem lambdaPositive_functionalEquation_not_criticalLine
    {beta gam c : ℝ} (hb0 : 1 / 2 < beta) (hb1 : beta < 1)
    (hc0 : beta - 1 / 2 < c) (hc1 : c < 1 / 2) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ feNeutralLogDensity beta gam c u) ∧
    (∀ σ : ℝ, c + 1 / 2 < σ →
      (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * feNeutralLogDensity beta gam c u) =
        feNeutralTransformReal beta gam c σ) ∧
    (∀ s : ℂ, feNeutralTransform beta gam c s + feNeutralTransform beta gam c (1 - s) = 0) ∧
    (∀ s : ℂ, feGauge beta gam c (1 - s) = feGauge beta gam c s) ∧
    feGauge beta gam c ((beta : ℂ) + (gam : ℂ) * I) = 0 ∧
    1 / 2 < ((beta : ℂ) + (gam : ℂ) * I).re ∧
    ((beta : ℂ) + (gam : ℂ) * I).re < 1 ∧
    c + 1 / 2 < 1 :=
  ⟨fun _ hu => feNeutralLogDensity_nonneg hb0 hc0 hu,
    fun _ hσ => integral_feNeutralLogDensity hb0 hc0 hσ,
    feNeutralTransform_antisymm beta gam c,
    feGauge_reflect beta gam c,
    feGauge_eq_zero beta gam c,
    by simpa using hb0,
    by simpa using hb1,
    by linarith⟩

end RHTower
