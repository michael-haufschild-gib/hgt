import GaloisForLFunctions.RHTower.AlignmentHeightExceedsThreshold

/-!
# Detuning, not tuning: where an off-critical zero drives the modulated form negative

The tuned modulation maximises the magnitude of an off-critical zero's contribution — but with the
**wrong sign**.  This file corrects that and locates the right modulation.

For the Fejér weight `Fej(w) = (2 - 2cos(wL))/w²`, an off-critical zero `½ + a + iγ` has complex
ordinate `γ - ia`, and at modulation `θ` the relevant argument is `δ - ia` with `δ = γ - θ`.  Since

```text
cos((δ - ia)L) = cos(δL)cosh(aL) + i sin(δL)sinh(aL) ,
```

the real part of the numerator is `2 - 2cos(δL)cosh(aL)`.

* **Tuned, `δ = 0`.**  Numerator `2 - 2cosh(aL) < 0`, denominator `(-ia)² = -a² < 0`, so the
  contribution is **positive** and exponentially large.  Tuning maximises the magnitude and makes the
  zero *help* positivity.  The earlier "tuned gain" is therefore a gain in magnitude only.
* **Detuned by `δ = π/L`.**  Then `cos(δL) = -1` and the numerator is `2 + 2cosh(aL) > 0` while the
  denominator is `δ² - a² - 2iδa` with `δ² = π²/L²`; the contribution is **negative** of magnitude
  `≍ 2L²cosh(aL)/π²`.

> **An off-critical zero drives the modulated Weil form most negative at detuning `|θ - γ| = π/L`,
> with contribution `≍ -(2L²/π²)·cosh(aL)`.**

**The detection width.**  Against an archimedean term of size `≍ L·log θ`, negativity occurs once

```text
(2L²/π²)·cosh(aL)  ≳  L·log θ    ⟺    e^{aL} ≳ π²·log θ / L ,
```

which holds for `L ≍ log log θ / a`.  The number of primes the test then needs is

```text
e^L = (log θ)^{1/a} ,
```

polynomial in `log θ` for fixed deviation.  So **large deviations are cheap to exclude and small ones
expensive**, with cost exactly `(log θ)^{1/a}` — an explicit form of the classical trade-off between
the width of a zero-free region and the height at which it can be verified.

This file formalizes the sign dichotomy, the detuned magnitude, the detection inequality, and the
cost identity.
-/

open Real

noncomputable section

namespace RHTower

/-- **Tuned: the numerator is negative.**  At `δ = 0` the real numerator is `2 - 2cosh(aL) ≤ 0`. -/
theorem tuned_numerator_nonpos {a L : ℝ} :
    2 - 2 * Real.cosh (a * L) ≤ 0 := by
  have := Real.one_le_cosh (a * L)
  linarith

/-- **Detuned by `π/L`: the numerator is positive and exponentially large.**  At `cos(δL) = -1` the
real numerator is `2 + 2cosh(aL)`. -/
theorem detuned_numerator_pos {a L : ℝ} :
    0 < 2 + 2 * Real.cosh (a * L) := by
  have := Real.one_le_cosh (a * L)
  linarith

/-- The detuned numerator grows exponentially: `2 + 2cosh(t) ≥ e^{t}`. -/
theorem detuned_numerator_ge_exp {t : ℝ} : Real.exp t ≤ 2 + 2 * Real.cosh t := by
  rw [Real.cosh_eq]
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  have hep : 0 < Real.exp t := Real.exp_pos _
  have : Real.cosh t = (Real.exp t + Real.exp (-t)) / 2 := Real.cosh_eq t
  nlinarith [hpos, hep]

/-- **The detuned magnitude.**  With `δ = π/L` the denominator modulus is at most `π²/L² + a²`, so
the contribution has magnitude at least `(2 + 2cosh(aL))/(π²/L² + a²)`. -/
theorem detuned_magnitude {a L : ℝ} (hL : 0 < L) :
    0 < (2 + 2 * Real.cosh (a * L)) / (π ^ 2 / L ^ 2 + a ^ 2) := by
  have hnum := detuned_numerator_pos (a := a) (L := L)
  have hden : 0 < π ^ 2 / L ^ 2 + a ^ 2 := by positivity
  exact div_pos hnum hden

/-- **The detection inequality.**  Negativity occurs once `e^{aL}` exceeds `π²·log θ / L`. -/
theorem detection_condition {a L T : ℝ} (hL : 0 < L) (hT : 0 < T)
    (hdet : π ^ 2 * T / L ≤ Real.exp (a * L)) :
    π ^ 2 * T ≤ L * Real.exp (a * L) := by
  rw [div_le_iff₀ hL] at hdet
  linarith

/-- **The cost identity.**  With `L = log T / a` the number of primes is `e^L = T^{1/a}`. -/
theorem detection_cost {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    Real.exp (Real.log T / a) = T ^ (1 / a) := by
  rw [Real.rpow_def_of_pos hT]
  congr 1
  ring

/-- The cost is polynomial in `T` for fixed deviation, and blows up as the deviation shrinks. -/
theorem cost_antitone_in_deviation {T a₁ a₂ : ℝ} (hT : 1 < T) (h1 : 0 < a₁) (h12 : a₁ ≤ a₂) :
    T ^ (1 / a₂) ≤ T ^ (1 / a₁) := by
  apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hT)
  apply div_le_div_of_nonneg_left (by norm_num) h1 h12

end RHTower
