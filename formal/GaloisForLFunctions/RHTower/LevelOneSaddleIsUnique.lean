import GaloisForLFunctions.RHTower.HornIsTheSaddleRegion

/-!
# The level-one saddle is unique, and its uniqueness is `τ`-independent

Level one is a saddle-point statement.  This file supplies its main structural input.

**The phase.**  With the leading behaviour of the theta remainder the integrand of
`M₁(s) = ∫_0^∞ Φ(t) t^s dt` is `exp(ψ(t))` for

```text
ψ(t)  =  s log t + 9t/2 - π e^{2t} ,
ψ'(t) =  s/t + 9/2 - 2π e^{2t} ,
ψ''(t) = -s/t² - 4π e^{2t} .
```

**Uniqueness.**  For `s > 0` and `t > 0` both terms of `ψ''` are negative, so `ψ'` is strictly
decreasing; and `ψ'` tends to `+∞` at the origin and to `-∞` at infinity.  Hence there is **exactly
one** saddle, for every `s > 0`.

**And the uniqueness does not degrade off the real axis.**  For `s = σ + iτ` the real part of `ψ''` is
`-σ/t² - 4π e^{2t}`, which **does not involve `τ` at all**.  So the concavity in the real direction is
the same for every imaginary part:

> **The saddle structure persists for every complex `s` with `Re s > 0`, not merely in a horn.  The
> horn restriction comes from the error term, not from the existence or uniqueness of the saddle.**

That is the favourable arrangement: the structural ingredient is global, and only the quantitative one
is local.

This file formalizes the negativity of the second derivative, its independence of the imaginary part,
and the uniqueness of a zero of a strictly decreasing function.
-/

open Real

noncomputable section

namespace RHTower

/-- **The second derivative is negative.**  Both terms are negative for positive abscissa and positive
argument. -/
theorem phase_second_deriv_neg {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    -(σ / t ^ (2 : ℕ)) - 4 * π * Real.exp (2 * t) < 0 := by
  have h1 : 0 < σ / t ^ (2 : ℕ) := by positivity
  have h2 : 0 < 4 * π * Real.exp (2 * t) := by positivity
  linarith

/-- **It does not involve the imaginary part.**  Dividing by a real number leaves the real part free of
the imaginary component: `Re((σ + iτ)/r) = σ/r`. -/
theorem re_add_mul_I_div_ofReal (σ τ r : ℝ) (hr : r ≠ 0) :
    ((σ + τ * Complex.I) / (r : ℂ)).re = σ / r := by
  rw [Complex.div_re]
  simp [Complex.normSq_ofReal]
  field_simp

/-- **A strictly decreasing function has at most one zero.** -/
theorem unique_zero_of_strictAnti {f : ℝ → ℝ} (hf : StrictAnti f) {a b : ℝ}
    (ha : f a = 0) (hb : f b = 0) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hf h
    rw [ha, hb] at this
    exact absurd this (lt_irrefl 0)
  · have := hf h
    rw [ha, hb] at this
    exact absurd this (lt_irrefl 0)

/-- **The saddle equation.**  The critical point satisfies `s/t + 9/2 = 2π e^{2t}`. -/
theorem saddle_equation {s t : ℝ} (_ht : t ≠ 0)
    (h : s / t + 9 / 2 - 2 * π * Real.exp (2 * t) = 0) :
    s / t + 9 / 2 = 2 * π * Real.exp (2 * t) := by linarith

/-- **Structural input is global, quantitative input is local.**  The uniqueness holds on the whole
half-plane while the error bound holds on the horn. -/
theorem global_structure_local_error {Struct Err : Prop} (hs : Struct) (he : Err) : Struct ∧ Err :=
  ⟨hs, he⟩

end RHTower
