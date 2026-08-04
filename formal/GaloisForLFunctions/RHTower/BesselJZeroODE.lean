import GaloisForLFunctions.RHTower.BesselJZeroEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Bessel's equation for the order-zero integral representation

The function `besselJ0 u = (1/pi) int_0^pi cos(u sin θ) dθ` is differentiated twice under the integral
sign and shown to satisfy Bessel's equation of order zero,

```text
J_0''(u) + J_0'(u)/u + J_0(u) = 0,      u ≠ 0.
```

The mechanism is one integration by parts.  Differentiation gives
`J_0''(u) + J_0(u) = (1/pi) int_0^pi cos²θ cos(u sin θ) dθ`, and since
`cos θ cos(u sin θ) = (1/u) d/dθ sin(u sin θ)`, integrating by parts against the second `cos θ`
returns exactly `-J_0'(u)/u`; the boundary terms vanish because `sin(u sin θ)` does at both ends.

* `besselJ0Deriv`, `besselJ0SecondDeriv` — the two differentiated integrals.
* `hasDerivAt_besselJ0`, `hasDerivAt_besselJ0Deriv` — differentiation under the integral sign, with the
  constant bound `1` as dominating function.
* `integral_sin_mul_sin_eq` — the integration-by-parts identity, valid for every `u`.
* **`besselJ0_ode`** — Bessel's equation.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-! ## The differentiated integrals -/

/-- The derivative of the order-zero Bessel function, as an integral. -/
def besselJ0Deriv (u : ℝ) : ℝ :=
  -(1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)

/-- The second derivative of the order-zero Bessel function, as an integral. -/
def besselJ0SecondDeriv (u : ℝ) : ℝ :=
  -(1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 2 * Real.cos (u * Real.sin θ)

theorem continuous_sin_mul_sin (u : ℝ) :
    Continuous fun θ : ℝ => Real.sin θ * Real.sin (u * Real.sin θ) := by fun_prop

theorem continuous_sin_sq_mul_cos (u : ℝ) :
    Continuous fun θ : ℝ => Real.sin θ ^ 2 * Real.cos (u * Real.sin θ) := by fun_prop

theorem continuous_cos_sq_mul_cos (u : ℝ) :
    Continuous fun θ : ℝ => Real.cos θ ^ 2 * Real.cos (u * Real.sin θ) := by fun_prop

/-! ## Differentiation under the integral sign -/

theorem hasDerivAt_besselJ0 (u : ℝ) : HasDerivAt besselJ0 (besselJ0Deriv u) u := by
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi) (bound := fun _ : ℝ => (1 : ℝ))
    (F := fun (x : ℝ) (θ : ℝ) => Real.cos (x * Real.sin θ))
    (F' := fun (x : ℝ) (θ : ℝ) => -(Real.sin θ * Real.sin (x * Real.sin θ)))
    (x₀ := u) (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_cos_mul_sin x).aestronglyMeasurable).restrict)
    ((continuous_cos_mul_sin u).intervalIntegrable _ _)
    (((continuous_sin_mul_sin u).neg.aestronglyMeasurable).restrict)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      rw [norm_neg, Real.norm_eq_abs, abs_mul]
      have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      have h2 : |Real.sin (x * Real.sin θ)| ≤ 1 := Real.abs_sin_le_one _
      nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.sin (x * Real.sin θ))])
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      have hinner : HasDerivAt (fun y : ℝ => y * Real.sin θ) (Real.sin θ) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.sin θ)
      have h := (Real.hasDerivAt_cos (x * Real.sin θ)).comp x hinner
      have hval : -Real.sin (x * Real.sin θ) * Real.sin θ
          = -(Real.sin θ * Real.sin (x * Real.sin θ)) := by ring
      rw [hval] at h
      exact h)
  have hderiv := hmain.2
  have hval : (∫ θ in (0 : ℝ)..Real.pi, -(Real.sin θ * Real.sin (u * Real.sin θ)))
      = -∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ) :=
    intervalIntegral.integral_neg
  rw [hval] at hderiv
  have h := hderiv.const_mul (1 / Real.pi)
  have hb : besselJ0 = fun x : ℝ => 1 / Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
      Real.cos (x * Real.sin θ) := rfl
  rw [hb]
  have hvalue : 1 / Real.pi * -∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ)
      = besselJ0Deriv u := by
    rw [besselJ0Deriv]
    ring
  rw [← hvalue]
  exact h

theorem hasDerivAt_besselJ0Deriv (u : ℝ) :
    HasDerivAt besselJ0Deriv (besselJ0SecondDeriv u) u := by
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := Real.pi) (bound := fun _ : ℝ => (1 : ℝ))
    (F := fun (x : ℝ) (θ : ℝ) => Real.sin θ * Real.sin (x * Real.sin θ))
    (F' := fun (x : ℝ) (θ : ℝ) => Real.sin θ ^ 2 * Real.cos (x * Real.sin θ))
    (x₀ := u) (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_sin_mul_sin x).aestronglyMeasurable).restrict)
    ((continuous_sin_mul_sin u).intervalIntegrable _ _)
    (((continuous_sin_sq_mul_cos u).aestronglyMeasurable).restrict)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin θ))]
      have h1 : Real.sin θ ^ 2 ≤ 1 := by
        nlinarith [Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ), sq_abs (Real.sin θ)]
      have h2 : |Real.cos (x * Real.sin θ)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [sq_nonneg (Real.sin θ), abs_nonneg (Real.cos (x * Real.sin θ))])
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ x _ => by
      have hinner : HasDerivAt (fun y : ℝ => y * Real.sin θ) (Real.sin θ) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.sin θ)
      have h := ((Real.hasDerivAt_sin (x * Real.sin θ)).comp x hinner).const_mul (Real.sin θ)
      have hval : Real.sin θ * (Real.cos (x * Real.sin θ) * Real.sin θ)
          = Real.sin θ ^ 2 * Real.cos (x * Real.sin θ) := by ring
      rw [hval] at h
      exact h)
  have hderiv := hmain.2
  have h := hderiv.const_mul (-(1 / Real.pi))
  have hb : besselJ0Deriv = fun x : ℝ => -(1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ * Real.sin (x * Real.sin θ) := rfl
  rw [hb]
  exact h

/-! ## The integration by parts -/

/-- The boundary terms vanish, so integrating `cos θ · d/dθ sin(u sin θ)` by parts turns the first
moment of `sin(u sin θ)` into the `cos²`-weighted cosine integral. -/
theorem integral_sin_mul_sin_eq (u : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ))
      = u * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cos (u * Real.sin θ) := by
  have hf : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi, HasDerivAt Real.cos (-Real.sin x) x :=
    fun x _ => Real.hasDerivAt_cos x
  have hg : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun θ : ℝ => Real.sin (u * Real.sin θ))
        (u * Real.cos x * Real.cos (u * Real.sin x)) x := by
    intro x _
    have hinner : HasDerivAt (fun θ : ℝ => u * Real.sin θ) (u * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul u
    have h := (Real.hasDerivAt_sin (u * Real.sin x)).comp x hinner
    have hval : Real.cos (u * Real.sin x) * (u * Real.cos x)
        = u * Real.cos x * Real.cos (u * Real.sin x) := by ring
    rw [hval] at h
    exact h
  have hf' : IntervalIntegrable (fun x : ℝ => -Real.sin x) volume 0 Real.pi :=
    (Real.continuous_sin.neg).intervalIntegrable _ _
  have hg' : IntervalIntegrable
      (fun x : ℝ => u * Real.cos x * Real.cos (u * Real.sin x)) volume 0 Real.pi := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hg hf' hg'
  have hbdry : Real.cos Real.pi * Real.sin (u * Real.sin Real.pi)
      - Real.cos 0 * Real.sin (u * Real.sin 0) = 0 := by
    simp
  rw [hbdry] at hibp
  have hleft : (∫ x in (0 : ℝ)..Real.pi,
      Real.cos x * (u * Real.cos x * Real.cos (u * Real.sin x)))
      = u * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cos (u * Real.sin θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  have hright : (∫ x in (0 : ℝ)..Real.pi, -Real.sin x * Real.sin (u * Real.sin x))
      = -∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (u * Real.sin θ) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [hleft, hright] at hibp
  linarith [hibp]

/-! ## Bessel's equation -/

/-- The `cos²`-weighted cosine integral is the sum of the second derivative and the value. -/
theorem besselJ0SecondDeriv_add_besselJ0 (u : ℝ) :
    besselJ0SecondDeriv u + besselJ0 u
      = (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cos (u * Real.sin θ) := by
  have hsub : (∫ θ in (0 : ℝ)..Real.pi, Real.cos (u * Real.sin θ))
      - ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 2 * Real.cos (u * Real.sin θ)
      = ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cos (u * Real.sin θ) := by
    rw [← intervalIntegral.integral_sub ((continuous_cos_mul_sin u).intervalIntegrable _ _)
      ((continuous_sin_sq_mul_cos u).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hpy : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hpy]
    ring
  rw [besselJ0SecondDeriv, besselJ0, ← hsub]
  ring

/-- **Bessel's equation of order zero.**  The integral representation is a genuine solution, so the
whole Liouville–Green theory of the equation applies to it. -/
theorem besselJ0_ode {u : ℝ} (hu : u ≠ 0) :
    besselJ0SecondDeriv u + besselJ0Deriv u / u + besselJ0 u = 0 := by
  have hkey := integral_sin_mul_sin_eq u
  have hsum := besselJ0SecondDeriv_add_besselJ0 u
  have hd : besselJ0Deriv u / u
      = -(1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ 2 * Real.cos (u * Real.sin θ) := by
    rw [besselJ0Deriv, hkey]
    field_simp
  rw [hd] at *
  linarith [hsum]

end GaloisForLFunctions.RHTower

end
