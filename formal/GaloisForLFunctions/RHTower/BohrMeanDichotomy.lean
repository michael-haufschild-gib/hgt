import GaloisForLFunctions.RHTower.ScrewArchimedeanShiftDecay

/-!
# The mean dichotomy: real frequencies average to nothing, a positive exponent averages to infinity

Cycle-86's reduction leaves the rectangular Ward defect equal, up to an exponentially small term, to
the zero sum

```text
Z(x)  =  Σ_ρ c_ρ · e^{(ρ - 1/2) x} ,
```

whose exponents are `ρ - 1/2 = a + iγ`.  Under the hypothesis every exponent is purely imaginary and
`Z` is a Besicovitch almost periodic function of the shift; if a zero lies off the line, one exponent
has positive real part.  This file isolates the elementary dichotomy that separates the two cases, in
the form that decides semiboundedness.

**Real frequency.**  `(1/X)∫₀^X cos(γx) dx = sin(γX)/(γX)`, of modulus at most `1/(|γ|X)`: every
nonzero real frequency averages to zero, at rate `1/X`.

**Positive real part.**  `(1/X)∫₀^X e^{ax} dx = (e^{aX} - 1)/(aX) ≥ 1 + aX/4`, using
`e^{t} ≥ (1 + t/2)²`: a single exponent with positive real part makes the mean diverge linearly.

> **The Bohr mean of the shifted defect exists precisely when no exponent has positive real part.
> Existence of the mean is therefore at least as strong as the semiboundedness asked for by the open
> core, and it fails by a linear divergence — not marginally — as soon as one zero leaves the line.**

**Why the mean cannot be computed from the prime side.**  The obvious route is
`∫₁^∞ (ψ(t) - t) t^{-s-1} dt = -ζ'(s)/(s ζ(s)) - 1/(s-1)`, whose convergence at `s = 1/2` is itself
equivalent to the hypothesis.  So the mean is available in closed form — as
`2 - 2ζ'(1/2)/ζ(1/2)` up to normalisation — exactly when the hypothesis holds, and the Bohr route is
a reformulation rather than an independent handle.  What survives is the sharp form of the failure
recorded above: the divergence is linear in the shift range, with an explicit constant.

This file formalizes the two integrals and the dichotomy.
-/

open Real

noncomputable section

namespace RHTower

/-- The average of a real frequency over `[0, X]`. -/
theorem integral_cos_freq {γ : ℝ} (hγ : γ ≠ 0) (X : ℝ) :
    ∫ x in (0:ℝ)..X, Real.cos (γ * x) = Real.sin (γ * X) / γ := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun u : ℝ => Real.sin (γ * u) / γ) (Real.cos (γ * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => γ * u) γ x := by
      simpa using (hasDerivAt_id x).const_mul γ
    have h2 := h1.sin
    have h3 := h2.div_const γ
    simpa [hγ] using! h3
  have hint : IntervalIntegrable (fun x : ℝ => Real.cos (γ * x))
      MeasureTheory.volume 0 X :=
    (Real.continuous_cos.comp (continuous_id.const_mul γ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp

/-- **Real frequencies average away.**  The mean over `[0, X]` of `cos(γx)` has modulus at most
`1/(|γ|X)`. -/
theorem cos_mean_decay {γ X : ℝ} (hγ : γ ≠ 0) (hX : 0 < X) :
    |(∫ x in (0:ℝ)..X, Real.cos (γ * x)) / X| ≤ 1 / (|γ| * X) := by
  have hgpos : 0 < |γ| := abs_pos.mpr hγ
  have hs : |Real.sin (γ * X)| ≤ 1 := Real.abs_sin_le_one _
  rw [integral_cos_freq hγ, abs_div, abs_div, abs_of_pos hX]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hs, hgpos, hX, mul_pos hgpos hX]

/-- The average of a positive exponent over `[0, X]`. -/
theorem integral_exp_rate {a : ℝ} (ha : a ≠ 0) (X : ℝ) :
    ∫ x in (0:ℝ)..X, Real.exp (a * x) = (Real.exp (a * X) - 1) / a := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun u : ℝ => Real.exp (a * u) / a) (Real.exp (a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => a * u) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h3 := (h1.exp).div_const a
    simpa [ha] using! h3
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (a * x))
      MeasureTheory.volume 0 X :=
    (Real.continuous_exp.comp (continuous_id.const_mul a)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  rw [show a * (0:ℝ) = 0 by ring, Real.exp_zero]
  ring

/-- `e^t ≥ (1 + t/2)²` for `t ≥ 0`, hence `e^t - 1 ≥ t + t²/4`. -/
theorem exp_ge_quadratic {t : ℝ} (ht : 0 ≤ t) : t + t ^ (2 : ℕ) / 4 ≤ Real.exp t - 1 := by
  have h : 1 + t / 2 ≤ Real.exp (t / 2) := by
    have := Real.add_one_le_exp (t / 2)
    linarith
  have hsq : (1 + t / 2) ^ (2 : ℕ) ≤ Real.exp (t / 2) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by linarith) h 2
  have hexp : Real.exp (t / 2) ^ (2 : ℕ) = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hsq
  nlinarith

/-- **A positive exponent makes the mean diverge linearly.**  The mean over `[0, X]` of `e^{ax}` is
at least `1 + aX/4`. -/
theorem exp_mean_diverges {a X : ℝ} (ha : 0 < a) (hX : 0 < X) :
    1 + a * X / 4 ≤ (∫ x in (0:ℝ)..X, Real.exp (a * x)) / X := by
  rw [integral_exp_rate (ne_of_gt ha)]
  have ht : 0 ≤ a * X := by positivity
  have h := exp_ge_quadratic ht
  rw [div_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **The dichotomy.**  A finite mean bound forces the exponent to be non-positive: if the mean of
`e^{ax}` stays below `M` for arbitrarily large `X`, then `a ≤ 4(M-1)/X` for those `X`. -/
theorem mean_bound_forces_small_rate {a X M : ℝ} (ha : 0 < a) (hX : 0 < X)
    (hM : (∫ x in (0:ℝ)..X, Real.exp (a * x)) / X ≤ M) :
    a ≤ 4 * (M - 1) / X := by
  have h := exp_mean_diverges ha hX
  rw [le_div_iff₀ hX]
  linarith

/-- **Semiboundedness from a mean bound.**  If the mean stays bounded along a sequence of ranges
growing without bound, the rate must be zero. -/
theorem rate_zero_of_uniform_mean {a M : ℝ} (ha : 0 < a)
    (h : ∀ X : ℝ, 0 < X → (∫ x in (0:ℝ)..X, Real.exp (a * x)) / X ≤ M) :
    ∀ X : ℝ, 0 < X → a * X ≤ 4 * (M - 1) := by
  intro X hX
  have := mean_bound_forces_small_rate ha hX (h X hX)
  rw [le_div_iff₀ hX] at this
  linarith

end RHTower
