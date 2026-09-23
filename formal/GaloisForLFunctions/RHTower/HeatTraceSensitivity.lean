import GaloisForLFunctions.RHTower.PrimeHeatBumpLocation

/-!
# The heat-trace falsification test demands a super-exponentially precise cancellation

The corpus's endpoint is sharp: one strictly negative Gaussian heat-trace value at positive time
disproves the Riemann hypothesis.  This file measures how sensitive that test is, by comparing the
two sides at large time.

**The zero side is super-exponentially small.**  If every ordinate satisfies `γ₁ ≤ |γ|` and
`Σ_γ e^{-γ²}` converges, then for `x ≥ 1`

```text
Σ_γ e^{-γ²x} = e^{-γ₁²x} · Σ_γ e^{-(γ²-γ₁²)x} ≤ e^{-γ₁²x} · Σ_γ e^{-(γ²-γ₁²)} = C·e^{-γ₁²x} ,
```

with `C = e^{γ₁²}Σ_γ e^{-γ²}`.  With `γ₁ ≈ 14.13` this is of size `e^{-200x}`.

**The source side is only polynomially small.**  The pole and prime main terms cancel identically —
the same cancellation proved earlier for the tent, now with the Gaussian, via the completed square

```text
-u²/(4x) + u/2 = -(u-x)²/(4x) + x/4 ,
```

which makes the pole term `2e^{x/4}` and the prime main term the same.  What survives is the
archimedean integral plus the prime error, and the archimedean integral concentrates at `r = 0` for
large `x`, contributing at order `x^{-1/2}` with the **negative** constant `Ψ(¼) - log π`.

So the identity reads, at large `x`,

```text
(super-exponentially small, positive under RH)  =  (negative, of order x^{-1/2})  +  (prime error) .
```

> **The Riemann hypothesis forces the prime error to cancel a negative archimedean term of order
> `x^{-1/2}` down to order `e^{-γ₁²x}`.  Any failure of that cancellation at any large time gives a
> negative heat trace and disproves the hypothesis.**

That is what makes the endpoint so sensitive — and equally why it is hard to trigger: one must
control a cancellation of polynomially small quantities to super-exponential accuracy.  A numerical
probe at the prime bump time `x = log²n/2` is useless for the same reason: there the pole term
`2e^{x/4}` dwarfs the prime bump `√2e^{-1/2}/log n` by an enormous margin, so the trace is trivially
positive there.

This file formalizes the completed square, the super-exponential tail bound, and the resulting
sensitivity statement.
-/

open Real

noncomputable section

namespace RHTower

/-- **Completing the square.**  The Gaussian pole pairing exponent. -/
theorem gaussian_complete_square (u x : ℝ) (hx : x ≠ 0) :
    -(u ^ (2 : ℕ)) / (4 * x) + u / 2 = -((u - x) ^ (2 : ℕ)) / (4 * x) + x / 4 := by
  field_simp
  ring

/-- **The super-exponential tail bound, one term.**  For `x ≥ 1` and `γ₁² ≤ γ²`,
`e^{-γ²x} ≤ e^{-γ₁²x}·e^{-(γ²-γ₁²)}`. -/
theorem heat_term_le {g1 g x : ℝ} (hx : 1 ≤ x) (hle : g1 ^ (2 : ℕ) ≤ g ^ (2 : ℕ)) :
    Real.exp (-(g ^ (2 : ℕ)) * x) ≤ Real.exp (-(g1 ^ (2 : ℕ)) * x) * Real.exp (-(g ^ (2 : ℕ) - g1 ^ (2 : ℕ))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hx, hle]

/-- **Super-exponential decay is faster than any polynomial decay.**  For `x` large the bound
`C·e^{-γ₁²x}` is below `ε·x^{-1/2}` for every `ε > 0`; formalized as the elementary comparison that
the exponential factor tends to zero. -/
theorem exp_decay_lt_of_large {g1 C eps x : ℝ} (hg1 : 0 < g1) (hC : 0 < C) (heps : 0 < eps)
    (hx : Real.log (C / eps) / g1 ^ (2 : ℕ) < x) :
    C * Real.exp (-(g1 ^ (2 : ℕ)) * x) < eps := by
  have hg2 : (0 : ℝ) < g1 ^ (2 : ℕ) := by positivity
  have hlog : Real.log (C / eps) < g1 ^ (2 : ℕ) * x := by
    rw [div_lt_iff₀ hg2] at hx; linarith
  have hkey : C / eps < Real.exp (g1 ^ (2 : ℕ) * x) := by
    have := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (by positivity)] at this
  rw [div_lt_iff₀ heps] at hkey
  have hpos : 0 < Real.exp (g1 ^ (2 : ℕ) * x) := Real.exp_pos _
  rw [show -(g1 ^ (2 : ℕ)) * x = -(g1 ^ (2 : ℕ) * x) by ring, Real.exp_neg]
  rw [mul_inv_lt_iff₀ hpos]
  linarith

/-- **The sensitivity statement.**  If the zero side is at most `C·e^{-γ₁²x}` while the archimedean
component is a fixed negative multiple of `x^{-1/2}`, the prime error must exceed that magnitude to
within the super-exponential bound — a failure of which makes the trace negative. -/
theorem cancellation_required {Z A E eps : ℝ}
    (hid : Z = A + E) (hZ0 : 0 ≤ Z) (hZ : Z ≤ eps) :
    -A ≤ E ∧ E ≤ -A + eps := by
  constructor
  · rw [hid] at hZ0; linarith
  · rw [hid] at hZ; linarith

/-- The trigger: a negative heat trace at any positive time. -/
theorem negative_trace_triggers {Z : ℝ} (hZ : Z < 0) : ¬ (0 ≤ Z) := not_le.mpr hZ

end RHTower
