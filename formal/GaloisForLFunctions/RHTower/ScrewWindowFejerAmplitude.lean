import GaloisForLFunctions.RHTower.WardDefectFreedomVacuous

/-!
# The window curvature is a Fejér-weighted cosine series over the zeros

The prime side of the rectangular window curvature is a tent-weighted Chebyshev window.  This file
computes the **zero side** and finds the matching object: the same rectangular test function, seen
through its Fourier transform.

A critical zero contributes the screw term `(1 - cos(tγ))/γ²`.  Its step-`L` second difference is
governed by

```text
cos A - 2cos(A-θ) + cos(A-2θ) = -4 sin²(θ/2)·cos(A-θ) ,
```

so with `A = xγ` and `θ = Lγ` the contribution to the window curvature is

```text
(4 sin²(Lγ/2) / γ²) · cos((x-L)γ) .
```

The amplitude is exactly the squared modulus of the Fourier transform of the indicator of `[0,L]`,

```text
|∫₀^L e^{-iγu} du|² = (2 - 2cos(Lγ))/γ² = 4 sin²(Lγ/2)/γ² ,
```

confirming that the window curvature is the Weil form of the rectangular test function seen on the
zero side, with **nonnegative Fejér weights**.

Two consequences.

* The amplitude is at most `4/γ²`, so the critical part of the window curvature is an **absolutely
  convergent** cosine series and hence **uniformly bounded**: under the Riemann hypothesis the
  semiboundedness criterion holds automatically, with the explicit constant `B = -4Σ_γ γ^{-2}`.
* Everything unbounded therefore comes from off-critical zeros, whose exact exponential amplitude
  `e^{ta}/(2(a²+γ²))` is recorded separately.

So the open core, fully explicit, is a competition between a bounded Fejér cosine series over the
critical zeros and a tent-weighted Chebyshev window over the primes, with the off-critical zeros
supplying the only possible unbounded term.

This file formalizes the second-difference cosine identity, the Fejér amplitude, and the uniform
bound.
-/

open Real

noncomputable section

namespace RHTower

/-- **The second-difference cosine identity.**  Differencing a cosine twice at step `θ` multiplies it
by `-4sin²(θ/2)` and shifts the phase by `θ`. -/
theorem cos_secondDifference (A theta : ℝ) :
    Real.cos A - 2 * Real.cos (A - theta) + Real.cos (A - 2 * theta)
      = -4 * Real.sin (theta / 2) ^ 2 * Real.cos (A - theta) := by
  have h1 : Real.cos (A - theta) = Real.cos A * Real.cos theta + Real.sin A * Real.sin theta :=
    Real.cos_sub A theta
  have h2 : Real.cos (A - 2 * theta)
      = Real.cos A * Real.cos (2 * theta) + Real.sin A * Real.sin (2 * theta) :=
    Real.cos_sub A (2 * theta)
  have hc2 : Real.cos (2 * theta) = 2 * Real.cos theta ^ 2 - 1 := Real.cos_two_mul theta
  have hs2 : Real.sin (2 * theta) = 2 * Real.sin theta * Real.cos theta := Real.sin_two_mul theta
  have hhalf : Real.sin (theta / 2) ^ 2 = 1 / 2 - Real.cos theta / 2 := by
    have h := Real.sin_sq_eq_half_sub (theta / 2)
    have hd : 2 * (theta / 2) = theta := by ring
    rwa [hd] at h
  rw [h1, h2, hc2, hs2, hhalf]
  ring

/-- **The critical screw term's second difference.**  The contribution of a critical zero to the
window curvature is a cosine with Fejér amplitude. -/
theorem critical_screw_secondDifference {gam : ℝ} (hg : gam ≠ 0) (L x : ℝ) :
    (1 - Real.cos (x * gam)) / gam ^ 2
        - 2 * ((1 - Real.cos ((x - L) * gam)) / gam ^ 2)
        + (1 - Real.cos ((x - 2 * L) * gam)) / gam ^ 2
      = 4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 * Real.cos ((x - L) * gam) := by
  have hg2 : (gam : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hid : Real.cos (x * gam) - 2 * Real.cos (x * gam - L * gam)
      + Real.cos (x * gam - 2 * L * gam)
      = -4 * Real.sin (L * gam / 2) ^ 2 * Real.cos (x * gam - L * gam) := by
    have h := cos_secondDifference (x * gam) (L * gam)
    have e : x * gam - 2 * (L * gam) = x * gam - 2 * L * gam := by ring
    rwa [e] at h
  have hA : (x - L) * gam = x * gam - L * gam := by ring
  have hB : (x - 2 * L) * gam = x * gam - 2 * L * gam := by ring
  rw [hA, hB]
  linear_combination -hid / gam ^ 2

/-- **The Fejér amplitude.**  `4sin²(Lγ/2) = 2 - 2cos(Lγ)`, the squared modulus of the Fourier
transform of the indicator of `[0,L]` times `γ²`. -/
theorem fejer_amplitude (L gam : ℝ) :
    4 * Real.sin (L * gam / 2) ^ 2 = 2 - 2 * Real.cos (L * gam) := by
  have h := Real.sin_sq_eq_half_sub (L * gam / 2)
  have hd : 2 * (L * gam / 2) = L * gam := by ring
  rw [hd] at h
  rw [h]; ring

/-- The Fejér weight is nonnegative. -/
theorem fejer_nonneg {gam : ℝ} (hg : gam ≠ 0) (L : ℝ) :
    0 ≤ 4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 := by
  have hg2 : (0 : ℝ) < gam ^ 2 := by positivity
  positivity

/-- **The uniform bound.**  The Fejér weight is at most `4/γ²`, so the critical part of the window
curvature is an absolutely convergent cosine series and hence uniformly bounded. -/
theorem fejer_le {gam : ℝ} (hg : gam ≠ 0) (L : ℝ) :
    4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 ≤ 4 / gam ^ 2 := by
  have hg2 : (0 : ℝ) < gam ^ 2 := by positivity
  have hs : Real.sin (L * gam / 2) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (L * gam / 2), sq_nonneg (Real.cos (L * gam / 2))]
  gcongr
  linarith

/-- Hence each critical term of the window curvature is bounded in absolute value by `4/γ²`,
uniformly in the aperture and the sample point. -/
theorem critical_term_abs_le {gam : ℝ} (hg : gam ≠ 0) (L x : ℝ) :
    |4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 * Real.cos ((x - L) * gam)| ≤ 4 / gam ^ 2 := by
  rw [abs_mul]
  have h1 : |4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2|
      = 4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 := abs_of_nonneg (fejer_nonneg hg L)
  have h2 : |Real.cos ((x - L) * gam)| ≤ 1 := Real.abs_cos_le_one _
  rw [h1]
  calc 4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 * |Real.cos ((x - L) * gam)|
      ≤ 4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left h2 (fejer_nonneg hg L)
    _ = 4 * Real.sin (L * gam / 2) ^ 2 / gam ^ 2 := by ring
    _ ≤ 4 / gam ^ 2 := fejer_le hg L

end RHTower
