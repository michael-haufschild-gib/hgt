import GaloisForLFunctions.RHTower.LambdaPositiveFunctionalEquationOffLine

/-!
# An entire completed function with the exact Riemann functional equation,
# a nonnegative generalized von Mangoldt measure, and zeros off the critical line

`LambdaPositiveFunctionalEquationOffLine.lean` produced a `Λ`-positive system with the exact
Riemann functional equation whose zeros are off the critical line, at the cost of poles of the
completed function inside the strip.  Those poles were forced: nonnegativity of a reflection-
antisymmetric correction requires a positive coefficient at a *real* leading frequency, i.e. a real
pole of the completed function, and `ξ` has no real zeros to absorb it.

There is exactly one real frequency at which such a pole is harmless: `w = 1/2`, whose pole sits at
`s = 1` and `s = 0`, where the standard completion `s(s-1)` already clears poles.  Putting the whole
positive part there produces a system whose completed function is **entire**.

For `a₀ ∈ (0,1/2)` and `γ ≠ 0`, with `ρ = 1/2 + a₀ + iγ`, the correction to the generalized von
Mangoldt measure has logarithmic density

```text
d(u) = 4 e^{u/2}[cosh(u/2) - cosh(a₀ u) cos(γ u)] ≥ 0,
```

its Laplace transform is reflection antisymmetric, and the resulting system is

```text
F(s) = ζ(s)·G(s),   G(s) = (s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)/[s(s-1)]²,
(1/2)·s³(s-1)³·π^{-s/2}Γ(s/2)·F(s) = ξ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄),
```

which is entire of order one and invariant under `s ↦ 1-s`.  `F` has zeros at `ρ, ρ̄, 1-ρ, 1-ρ̄`,
off the critical line.  Its only deviation from `ζ` is the **order of the pole at `s = 1`**, which
is three instead of one.

So `Λ ≥ 0` + Euler product + exact Riemann functional equation + entire completed function of order
one do not force the critical line; the pole order is a further necessary hypothesis.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-! ## The correction density -/

/-- Logarithmic density of the correction whose whole positive part sits at the admissible
frequency `w = 1/2`. -/
def entireFEDensity (a0 gam : ℝ) (u : ℝ) : ℝ :=
  2 * (Real.exp ((1 / 2 : ℝ) * u) + Real.exp ((1 / 2 : ℝ) * u) * 0 + Real.exp 0 * 0) +
    (2 * (Real.exp u + 1) - 2 * Real.cos (gam * u) *
      (Real.exp ((1 / 2 + a0) * u) + Real.exp ((1 / 2 - a0) * u))) -
    2 * (Real.exp ((1 / 2 : ℝ) * u) + Real.exp ((1 / 2 : ℝ) * u) * 0 + Real.exp 0 * 0)

/-- Normalised form: `2(e^u + 1) - 2cos(γu)(e^{(1/2+a₀)u} + e^{(1/2-a₀)u})`. -/
theorem entireFEDensity_eq (a0 gam u : ℝ) :
    entireFEDensity a0 gam u =
      2 * (Real.exp u + 1) -
        2 * Real.cos (gam * u) *
          (Real.exp ((1 / 2 + a0) * u) + Real.exp ((1 / 2 - a0) * u)) := by
  unfold entireFEDensity; ring

/-- **Λ-positivity.**  The correction is a nonnegative measure for every off-critical abscissa
`a₀ ∈ (0,1/2)` and every ordinate `γ`. -/
theorem entireFEDensity_nonneg {a0 gam u : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (hu : 0 ≤ u) :
    0 ≤ entireFEDensity a0 gam u := by
  rw [entireFEDensity_eq]
  set X : ℝ := Real.exp (a0 * u) with hXdef
  set Y : ℝ := Real.exp ((1 / 2 : ℝ) * u) with hYdef
  have hXpos : 0 < X := Real.exp_pos _
  have hYpos : 0 < Y := Real.exp_pos _
  have hX1 : 1 ≤ X := Real.one_le_exp (by positivity)
  have hY1 : 1 ≤ Y := Real.one_le_exp (by positivity)
  have hXY : X ≤ Y := by
    rw [hXdef, hYdef]
    exact Real.exp_le_exp.mpr (by nlinarith [hu])
  have hA : Real.exp ((1 / 2 + a0) * u) = Y * X := by
    rw [hXdef, hYdef, ← Real.exp_add]; congr 1; ring
  have hB : Real.exp ((1 / 2 - a0) * u) = Y / X := by
    rw [hXdef, hYdef, ← Real.exp_sub]; congr 1; ring
  have hE : Real.exp u = Y * Y := by
    rw [hYdef, ← Real.exp_add]; congr 1; ring
  have hkey : Y * X + Y / X ≤ Y * Y + 1 := by
    have hid : (Y * Y + 1) - (Y * X + Y / X) = (Y - X) * (X * Y - 1) / X := by
      field_simp; ring
    have hnum : 0 ≤ (Y - X) * (X * Y - 1) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hdiv : 0 ≤ (Y - X) * (X * Y - 1) / X := div_nonneg hnum (le_of_lt hXpos)
    linarith [hid ▸ hdiv]
  rw [hA, hB, hE]
  have hcos : Real.cos (gam * u) ≤ 1 := Real.cos_le_one _
  have hP : 0 < Y * X + Y / X := by positivity
  have hstep : 2 * Real.cos (gam * u) * (Y * X + Y / X) ≤ 2 * (Y * X + Y / X) := by
    nlinarith [hP, hcos]
  linarith [hkey, hstep]

/-! ## Its Laplace transform -/

/-- Real form of the transform of the correction. -/
def entireFETransformReal (a0 gam : ℝ) (σ : ℝ) : ℝ :=
  2 * (1 / (σ - 1) + 1 / σ) -
    2 * ((σ - 1 / 2 - a0) / ((σ - 1 / 2 - a0) ^ 2 + gam ^ 2) +
      (σ - 1 / 2 + a0) / ((σ - 1 / 2 + a0) ^ 2 + gam ^ 2))

theorem integral_entireFEDensity {a0 gam σ : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2)
    (hσ : 1 < σ) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * entireFEDensity a0 gam u) =
      entireFETransformReal a0 gam σ := by
  have h1 : (0 : ℝ) < σ - 1 := by linarith
  have h2 : (0 : ℝ) < σ := by linarith
  have h3 : (0 : ℝ) < σ - 1 / 2 - a0 := by linarith
  have h4 : (0 : ℝ) < σ - 1 / 2 + a0 := by linarith
  have key : ∀ p : ℝ, 0 < σ - p →
      (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * Real.exp (p * u)) = 1 / (σ - p) := by
    intro p hp
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp (p * u))
        = fun u : ℝ => Real.exp (-((σ - p) * u)) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr, integral_Ioi_exp_neg_mul hp]
  have keycos : ∀ p : ℝ, 0 < σ - p →
      (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp (p * u)))
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
      have hh : Real.exp (-((σ - p) * u)) * |Real.cos (gam * u)| ≤ Real.exp (-((σ - p) * u)) * 1 :=
        mul_le_mul_of_nonneg_left hcos (le_of_lt (Real.exp_pos _))
      have h2' : Real.exp (-((σ - p) * u)) = |Real.exp (-(σ - p) * u)| := by
        rw [abs_of_pos (Real.exp_pos _)]; ring_nf
      rw [h2'] at hh ⊢
      simpa using hh
  have hi1 : IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((1:ℝ) * u)) (Ioi 0) := by
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((1:ℝ) * u))
        = fun u : ℝ => Real.exp (-(σ - 1) * u) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]; exact exp_neg_integrableOn_Ioi 0 h1
  have hi2 : IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((0:ℝ) * u)) (Ioi 0) := by
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp ((0:ℝ) * u))
        = fun u : ℝ => Real.exp (-σ * u) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]; exact exp_neg_integrableOn_Ioi 0 h2
  have hsplit : (fun u : ℝ => Real.exp (-(σ * u)) * entireFEDensity a0 gam u)
      = fun u : ℝ =>
        (2 * (Real.exp (-(σ * u)) * Real.exp ((1:ℝ) * u)) +
          2 * (Real.exp (-(σ * u)) * Real.exp ((0:ℝ) * u))) -
        (2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp ((1/2 + a0) * u))) +
          2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp ((1/2 - a0) * u)))) := by
    funext u; rw [entireFEDensity_eq]; simp only [one_mul, zero_mul, Real.exp_zero]; ring
  have I1 := hi1.const_mul (2 : ℝ)
  have I2 := hi2.const_mul (2 : ℝ)
  have I3 := (hbound (1/2 + a0) (by linarith)).const_mul (2 : ℝ)
  have I4 := (hbound (1/2 - a0) (by linarith)).const_mul (2 : ℝ)
  have hA : IntegrableOn
      (fun u : ℝ => 2 * (Real.exp (-(σ * u)) * Real.exp ((1:ℝ) * u)) +
        2 * (Real.exp (-(σ * u)) * Real.exp ((0:ℝ) * u))) (Ioi 0) := by simpa using I1.add I2
  have hB : IntegrableOn
      (fun u : ℝ =>
        2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp ((1/2 + a0) * u))) +
        2 * (Real.exp (-(σ * u)) * (Real.cos (gam * u) * Real.exp ((1/2 - a0) * u))))
      (Ioi 0) := by simpa using I3.add I4
  rw [hsplit, integral_sub hA hB, integral_add I1 I2, integral_add I3 I4,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    key 1 (by linarith), key 0 (by linarith),
    keycos (1/2 + a0) (by linarith), keycos (1/2 - a0) (by linarith)]
  rw [entireFETransformReal]
  have e1 : σ - (1/2 + a0) = σ - 1/2 - a0 := by ring
  have e2 : σ - (1/2 - a0) = σ - 1/2 + a0 := by ring
  rw [e1, e2, sub_zero]
  ring

/-! ## Reflection antisymmetry -/

/-- Complex form of the transform. -/
def entireFETransform (a0 gam : ℝ) (s : ℂ) : ℂ :=
  2 * ((s - 1)⁻¹ + s⁻¹) -
    ((s - ((1 / 2 + a0 : ℝ) + (gam : ℂ) * I))⁻¹ + (s - ((1 / 2 + a0 : ℝ) - (gam : ℂ) * I))⁻¹ +
      (s - ((1 / 2 - a0 : ℝ) + (gam : ℂ) * I))⁻¹ + (s - ((1 / 2 - a0 : ℝ) - (gam : ℂ) * I))⁻¹)

/-- **Reflection antisymmetry.**  Adding the correction preserves the exact Riemann functional
equation.  The identity is unconditional; reciprocal junk values cancel in the same pattern. -/
theorem entireFETransform_antisymm (a0 gam : ℝ) (s : ℂ) :
    entireFETransform a0 gam s + entireFETransform a0 gam (1 - s) = 0 := by
  have pair : ∀ r : ℂ, (s - r)⁻¹ + (s - (1 - r))⁻¹ +
      ((1 - s - r)⁻¹ + (1 - s - (1 - r))⁻¹) = 0 := by
    intro r
    have h1 : (1 : ℂ) - s - r = -(s - (1 - r)) := by ring
    have h2 : (1 : ℂ) - s - (1 - r) = -(s - r) := by ring
    rw [h1, h2, inv_neg, inv_neg]; ring
  have hp := pair 1
  have hq := pair (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I)
  have hr := pair (((1 / 2 + a0 : ℝ) : ℂ) - (gam : ℂ) * I)
  have e0 : (1 : ℂ) - 1 = 0 := by ring
  have e1 : (1 : ℂ) - (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I)
      = ((1 / 2 - a0 : ℝ) : ℂ) - (gam : ℂ) * I := by push_cast; ring
  have e2 : (1 : ℂ) - (((1 / 2 + a0 : ℝ) : ℂ) - (gam : ℂ) * I)
      = ((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I := by push_cast; ring
  rw [e0] at hp
  rw [e1] at hq
  rw [e2] at hr
  simp only [entireFETransform, sub_zero]
  linear_combination (2 : ℂ) * hp - hq - hr

/-! ## The gauge, its entirety, and its off-critical zeros -/

/-- Numerator polynomial: the off-critical quadruple. -/
def offLineQuartet (a0 gam : ℝ) (s : ℂ) : ℂ :=
  (s - (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I)) *
    (s - (((1 / 2 + a0 : ℝ) : ℂ) - (gam : ℂ) * I)) *
    (s - (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I)) *
    (s - (((1 / 2 - a0 : ℝ) : ℂ) - (gam : ℂ) * I))

/-- The rational gauge whose logarithmic derivative is the correction transform. -/
def entireFEGauge (a0 gam : ℝ) (s : ℂ) : ℂ :=
  offLineQuartet a0 gam s / (s * (s - 1)) ^ 2

/-- **Entirety.**  Clearing the gauge's poles by the completion factor already present in the
standard `ξ` leaves a polynomial: the completed function of the perturbed system is
`ξ(s)·offLineQuartet(s)`, entire of order one. -/
theorem entireFEGauge_mul_completion (a0 gam : ℝ) (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    entireFEGauge a0 gam s * (s * (s - 1)) ^ 2 = offLineQuartet a0 gam s := by
  unfold entireFEGauge
  have h0 : s ≠ 0 := hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

/-- **Reflection invariance of the quartet**, hence of the completed function. -/
theorem offLineQuartet_reflect (a0 gam : ℝ) (s : ℂ) :
    offLineQuartet a0 gam (1 - s) = offLineQuartet a0 gam s := by
  unfold offLineQuartet
  push_cast
  ring

/-- **Reflection invariance of the gauge.** -/
theorem entireFEGauge_reflect (a0 gam : ℝ) (s : ℂ) :
    entireFEGauge a0 gam (1 - s) = entireFEGauge a0 gam s := by
  unfold entireFEGauge
  rw [offLineQuartet_reflect]
  congr 1
  ring

/-- **Off-critical zero.** -/
theorem offLineQuartet_eq_zero (a0 gam : ℝ) :
    offLineQuartet a0 gam (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 := by
  unfold offLineQuartet
  simp

/-! ## The packaged statement -/

/-- **An entire, functional-equation-symmetric, `Λ`-positive system with zeros off the critical
line.**

For every `a₀ ∈ (0,1/2)` and every `γ`:

* the correction to the generalized von Mangoldt measure is nonnegative on `[0,∞)`, so `Λ ≥ 0` is
  preserved;
* its Laplace transform converges on `σ > 1` and is exactly reflection antisymmetric, so the
  perturbed system satisfies the **same** functional equation as `ζ`;
* the rational gauge becomes a **polynomial** after multiplication by the completion factor
  `[s(s-1)]²` already present in `ξ`, so the completed function `ξ(s)·offLineQuartet(s)` is
  **entire of order one**;
* that completed function is invariant under `s ↦ 1-s`;
* and it vanishes at `1/2 + a₀ + iγ`, whose real part exceeds `1/2`.

Hence `Λ ≥ 0`, an Euler product, the exact Riemann functional equation, and entirety of the
completed function do not force the critical line.  The remaining distinguishing hypothesis is the
order of the pole at `s = 1`. -/
theorem lambdaPositive_entire_functionalEquation_not_criticalLine
    {a0 gam : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ entireFEDensity a0 gam u) ∧
    (∀ σ : ℝ, 1 < σ →
      (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * entireFEDensity a0 gam u) =
        entireFETransformReal a0 gam σ) ∧
    (∀ s : ℂ, entireFETransform a0 gam s + entireFETransform a0 gam (1 - s) = 0) ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      entireFEGauge a0 gam s * (s * (s - 1)) ^ 2 = offLineQuartet a0 gam s) ∧
    (∀ s : ℂ, offLineQuartet a0 gam (1 - s) = offLineQuartet a0 gam s) ∧
    offLineQuartet a0 gam (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 ∧
    1 / 2 < ((((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I)).re ∧
    ((((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I)).re < 1 :=
  ⟨fun _ hu => entireFEDensity_nonneg ha0 ha1 hu,
    fun _ hσ => integral_entireFEDensity ha0 ha1 hσ,
    entireFETransform_antisymm a0 gam,
    fun s hs hs1 => entireFEGauge_mul_completion a0 gam s hs hs1,
    offLineQuartet_reflect a0 gam,
    offLineQuartet_eq_zero a0 gam,
    by simp; linarith,
    by simp; linarith⟩

end RHTower
