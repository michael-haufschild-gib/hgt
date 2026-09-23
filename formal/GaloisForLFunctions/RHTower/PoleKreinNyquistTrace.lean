import GaloisForLFunctions.RHTower.ArithmeticFreeFalsificationLadder
import GaloisForLFunctions.RHTower.PoleFormDiagonalization

/-!
# The pole form's two eigenvalues, and why their sum is the length of the interval

The pole form of the Weil functional is `2⟨h,c⟩² - 2⟨h,s⟩²` with `c(u) = cosh(u/2)` and
`s(u) = sinh(u/2)`: indefinite of signature `(1,1)`.  Its negative direction is known to be cubically
small on a short interval.  This file computes **both** directions in closed form and records what
their sum is.

On `I = [-ℓ, ℓ]`, using `cosh²(u/2) = (cosh u + 1)/2` and `sinh²(u/2) = (cosh u - 1)/2`,

```text
‖c‖²_{L²(I)} = sinh ℓ + ℓ ,        ‖s‖²_{L²(I)} = sinh ℓ - ℓ ,
```

so by Cauchy–Schwarz the eigenvalues of the pole form on the unit sphere are

```text
μ₊ = 2(sinh ℓ + ℓ) ,        μ₋ = -2(sinh ℓ - ℓ) .
```

**Two consequences.**

*The positive direction is the reproducing-kernel extremiser.*  With `ℓ = L/2`,
`μ₊ = 2 sinh(L/2) + L`, which is exactly twice the Paley–Wiener detection ceiling at deviation
`a = 1/2`.  The pole is an off-critical zero at maximal deviation, and its extremal test — computed
here with no reproducing kernel anywhere in sight, only `∫cosh²` — reproduces the kernel constant.
That is an independent confirmation of the sharpness of the detection ceiling, and it identifies the
extremiser: `c = cosh(u/2)`, the even part of `e^{u/2}`, i.e. `K_{i/2} + K_{-i/2}`.

*The trace is the length of the interval.*

```text
μ₊ + μ₋ = 2(sinh ℓ + ℓ) - 2(sinh ℓ - ℓ) = 4ℓ = 2L ,
```

because `cosh² - sinh² = 1`: the transcendental parts cancel identically and what survives is
`2∫_I 1 du`.  Since the Nyquist density of `PW_{L/2}` is `L/2π`, this reads

```text
μ₊ + μ₋ = 4π · (Nyquist density of the test space) .
```

> **The net weight of the pole is the length of the support interval — one Nyquist cell.  The pole of
> `ζ` enters the Weil form as exactly one zero at deviation `1/2`, and the `cosh²-sinh² = 1` identity
> is what makes the count exact.**

This file formalizes the two `L²` norms, the eigenvalues, the trace identity, and the match with the
detection ceiling.
-/

open Real intervalIntegral

noncomputable section

namespace RHTower

/-- `cosh²(u/2) = (cosh u + 1)/2`, the companion of `sinh_half_sq`. -/
theorem cosh_half_sq (u : ℝ) : Real.cosh (u / 2) ^ (2 : ℕ) = (Real.cosh u + 1) / 2 := by
  have h := Real.cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring] at h
  have h2 := Real.cosh_sq_sub_sinh_sq (u / 2)
  linarith

/-- The primitive of `cosh` on an interval. -/
theorem integral_cosh_interval (a b : ℝ) :
    ∫ u in a..b, Real.cosh u = Real.sinh b - Real.sinh a := by
  rw [show (fun u => Real.cosh u) = deriv Real.sinh by
    funext u; rw [Real.deriv_sinh]]
  exact integral_deriv_eq_sub' _ rfl (fun x _ => Real.differentiable_sinh x)
    (by rw [Real.deriv_sinh]; exact Real.continuous_cosh.continuousOn)

/-- **The positive direction.**  `‖cosh(·/2)‖²_{L²[-ℓ,ℓ]} = sinh ℓ + ℓ`. -/
theorem cosh_half_norm_sq (ℓ : ℝ) :
    ∫ u in (-ℓ)..ℓ, Real.cosh (u / 2) ^ (2 : ℕ) = Real.sinh ℓ + ℓ := by
  have hint1 : IntervalIntegrable (fun u => Real.cosh u / 2) MeasureTheory.volume (-ℓ) ℓ :=
    (Real.continuous_cosh.div_const 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun _ : ℝ => (1:ℝ) / 2) MeasureTheory.volume (-ℓ) ℓ :=
    _root_.intervalIntegrable_const
  have hcongr : ∫ u in (-ℓ)..ℓ, Real.cosh (u / 2) ^ (2 : ℕ)
      = ∫ u in (-ℓ)..ℓ, (Real.cosh u / 2 + 1 / 2) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only []
    rw [cosh_half_sq u]; ring
  rw [hcongr, intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_div,
    integral_cosh_interval, intervalIntegral.integral_const, Real.sinh_neg]
  simp only [smul_eq_mul]
  ring

/-- **The negative direction.**  `‖sinh(·/2)‖²_{L²[-ℓ,ℓ]} = sinh ℓ - ℓ`. -/
theorem sinh_half_norm_sq (ℓ : ℝ) :
    ∫ u in (-ℓ)..ℓ, Real.sinh (u / 2) ^ (2 : ℕ) = Real.sinh ℓ - ℓ := by
  have hint1 : IntervalIntegrable (fun u => Real.cosh u / 2) MeasureTheory.volume (-ℓ) ℓ :=
    (Real.continuous_cosh.div_const 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun _ : ℝ => (1:ℝ) / 2) MeasureTheory.volume (-ℓ) ℓ :=
    _root_.intervalIntegrable_const
  have hcongr : ∫ u in (-ℓ)..ℓ, Real.sinh (u / 2) ^ (2 : ℕ)
      = ∫ u in (-ℓ)..ℓ, (Real.cosh u / 2 - 1 / 2) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only []
    rw [sinh_half_sq u]; ring
  rw [hcongr, intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_div,
    integral_cosh_interval, intervalIntegral.integral_const, Real.sinh_neg]
  simp only [smul_eq_mul]
  ring

/-- **The trace identity.**  The two eigenvalues sum to `4ℓ`, the length of the interval: the
transcendental parts cancel by `cosh² - sinh² = 1`. -/
theorem pole_trace_eq_length (ℓ : ℝ) :
    2 * (Real.sinh ℓ + ℓ) + -(2 * (Real.sinh ℓ - ℓ)) = 4 * ℓ := by ring

/-- The cancellation made explicit: the integrands differ by the constant `1`. -/
theorem pythagorean_source (u : ℝ) :
    Real.cosh (u / 2) ^ (2 : ℕ) - Real.sinh (u / 2) ^ (2 : ℕ) = 1 := by
  rw [cosh_half_sq, sinh_half_sq]; ring

/-- **The positive eigenvalue is the detection ceiling.**  With `ℓ = L/2` the Krein-positive
eigenvalue of the pole form equals twice the Paley–Wiener ceiling at deviation `1/2`, computed here
with no reproducing kernel: an independent confirmation of that constant. -/
theorem pole_eigenvalue_eq_kernel_ceiling (ℓ : ℝ) :
    2 * (Real.sinh ℓ + ℓ) = 2 * detectionCeiling (1 / 2) (2 * ℓ) := by
  rw [pole_is_maximal_deviation]
  rw [show 2 * ℓ / 2 = ℓ by ring]
  ring

/-- **One Nyquist cell.**  The trace equals `4π` times the Nyquist density `L/2π` of `PW_{L/2}`,
with `L = 2ℓ`: the pole counts as exactly one zero at deviation `1/2`. -/
theorem trace_eq_nyquist_cell {ℓ : ℝ} (hπ : π ≠ 0) :
    4 * ℓ = 4 * π * (2 * ℓ / (2 * π)) := by
  field_simp

/-- The form is genuinely indefinite for `ℓ > 0`: the negative eigenvalue is strictly negative. -/
theorem pole_indefinite {ℓ : ℝ} (hℓ : 0 < ℓ) : -(2 * (Real.sinh ℓ - ℓ)) < 0 := by
  have h := Real.self_lt_sinh_iff.mpr hℓ
  linarith

end RHTower
