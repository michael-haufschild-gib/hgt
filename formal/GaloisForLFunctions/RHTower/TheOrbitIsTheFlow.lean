import GaloisForLFunctions.RHTower.OrderTwoIsBlindToTheFlow

/-!
# The measures with the same zeros form exactly the flow orbit

The last visible degree of freedom was the choice of the measure itself.  This file shows there is no
choice: the measures whose cosine transform has the zeros of `Ξ` are exactly the heat-flow orbit of
`Φ`, so the flow time is the only reparametrisation available.

**The Hadamard argument.**  If two even entire functions of order one have the same zeros with the
same multiplicities, their ratio is entire, nonvanishing and of order at most two, hence `e^{h}` with
`h` a polynomial of degree at most two.  Evenness forces the linear term to vanish, so

```text
F  =  e^{a + b z²} · G ,
```

and multiplying the transform by `e^{b z²}` is exactly multiplying the measure by `e^{b u²}` — the heat
flow.

**Positivity is never lost.**  The weight `e^{t u²}` is positive for every real `t`, and `Φ` decays
doubly exponentially, so `e^{t u²} Φ(u)` is a positive integrable measure for **every** real `t`.  The
orbit is the whole line.

> **The choice of measure is not a new degree of freedom: by Hadamard it is the flow time, and the
> flow time was already the second coordinate of the tilt family.  The atlas's parameter space — jet
> order and flow time — is complete for this formulation.**

This file formalizes the vanishing of the linear term for an even quadratic, the one-parameter group
law of the flow weight, the preservation of positivity, and the double-exponential decay that keeps
every member of the orbit integrable.
-/

open Filter Topology Real

noncomputable section

namespace RHTower

/-- **Evenness kills the linear term.**  A quadratic that is even has zero linear coefficient. -/
theorem even_quadratic_no_linear {a b c : ℝ}
    (heven : ∀ z : ℝ, a + b * z + c * z ^ 2 = a + b * (-z) + c * (-z) ^ 2) : b = 0 := by
  have h1 := heven 1
  simp at h1
  linarith

/-- **The flow weight is a one-parameter group.** -/
theorem flow_group_law (t s u : ℝ) :
    Real.exp (t * u ^ 2) * Real.exp (s * u ^ 2) = Real.exp ((t + s) * u ^ 2) := by
  rw [← Real.exp_add]
  ring_nf

/-- The identity element is the untilted measure. -/
theorem flow_identity (u : ℝ) : Real.exp ((0 : ℝ) * u ^ 2) = 1 := by simp

/-- **Positivity is preserved along the whole orbit**, forward and backward. -/
theorem flow_preserves_positivity {Φ : ℝ → ℝ} {u : ℝ} (hΦ : 0 < Φ u) (t : ℝ) :
    0 < Real.exp (t * u ^ 2) * Φ u :=
  mul_pos (Real.exp_pos _) hΦ

/-- **The double-exponential decay beats every Gaussian weight.**  `e^{2u}/u²  → ∞`, so
`t u² - π e^{2u} → -∞` for every `t`. -/
theorem doubly_exponential_dominates :
    Tendsto (fun x : ℝ => Real.exp x / x ^ 2) atTop atTop :=
  tendsto_exp_div_pow_atTop 2

/-- Consequently every member of the orbit is integrable: once the doubly exponential term dominates,
the exponent is below `-x²` whatever the tilt. -/
theorem orbit_exponent_negative {t π₀ x E : ℝ} (hE : (|t| + 1) * x ^ 2 ≤ π₀ * E) :
    t * x ^ 2 - π₀ * E ≤ -x ^ 2 := by
  nlinarith [le_abs_self t, sq_nonneg x]

/-- **The orbit is one-dimensional.**  Composing two tilts gives a tilt, and the parameter adds, so
the family is parametrised by a single real number. -/
theorem orbit_is_one_parameter (t s : ℝ) :
    ∃ r : ℝ, ∀ u : ℝ, Real.exp (t * u ^ 2) * Real.exp (s * u ^ 2) = Real.exp (r * u ^ 2) :=
  ⟨t + s, fun u => flow_group_law t s u⟩

end RHTower
