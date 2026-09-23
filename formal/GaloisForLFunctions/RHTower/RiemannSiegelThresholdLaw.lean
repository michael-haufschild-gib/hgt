import GaloisForLFunctions.RHTower.ExplicitArchimedeanBaseline

/-!
# The elementary positivity threshold is the first zero of the Riemann–Siegel theta function

The stochastic-dominance bound of the previous module reads

```text
A(h)  ≥  (1/X) ∫_0^X σ(ξ) dξ ,     X = π/(2ℓ),   σ(ξ) = Re Ψ(1/4 + iξ/2) - log π ,
```

and the average has a closed form.  Since `d/dξ Im log Γ(1/4 + iξ/2) = (1/2) Re Ψ(1/4 + iξ/2)` and
`Γ(1/4)` is real,

```text
∫_0^X Re Ψ(1/4 + iξ/2) dξ = 2 Im log Γ(1/4 + iX/2) ,
```

so with the **Riemann–Siegel theta function** `θ(X) = Im log Γ(1/4 + iX/2) - (X/2) log π`,

```text
(1/X) ∫_0^X σ = (2/X)·Im log Γ(1/4 + iX/2) - log π = 2θ(X)/X .
```

The averaged archimedean symbol is therefore exactly `2θ(X)/X`, and its sign is the sign of `θ`.

Combining with the exact pole diagonalization and the cubic bound `sinh ℓ - ℓ ≤ (ℓ³/6)cosh ℓ`,

```text
pole(h) + A(h)  ≥  2P² - 2(sinh ℓ - ℓ) + 2θ(π/(2ℓ))·(2ℓ/π) ,
```

which is nonnegative as soon as `2θ(X)/X ≥ (ℓ³/3)cosh ℓ`.  The right side is at most about `0.005`
throughout the range of interest, so the threshold is governed by the sign of `θ`:

```text
2θ(X)/X ≥ 0  ⟺  X ≥ t₀ ,      t₀ = the first positive zero of θ ≈ 17.8455,
```

the first Gram point.  (Note `θ' = σ/2`, so the zero of `σ` at `≈ 6.29` is the *minimum* of `θ`, not
its zero; the two must not be conflated.)  With `X = π/(2ℓ)` this says

```text
ℓ ≤ ℓ₀ = π/(2t₀) ≈ 0.0880 ,
```

in close agreement with the Stirling estimate `1/(4e) ≈ 0.092` of the previous module — the exact
evaluation refines it rather than changing its order.  So the elementary archimedean-plus-pole
positivity range is cut off exactly at the first zero of the Riemann–Siegel theta function, against
the Connes–Consani range `ℓ < (log 2)/2 ≈ 0.3466`.

This file formalizes the closed-form identity for the averaged symbol, the integrated cubic bound
`sinh ℓ - ℓ ≤ (ℓ³/6)cosh ℓ`, the translation between the cutoff and the support half-length, and the
resulting positivity criterion.
-/

open Real

noncomputable section

namespace RHTower

/-- The averaged archimedean symbol, expressed through the Riemann–Siegel theta function. -/
def averagedSymbol (θ X : ℝ) : ℝ := 2 * θ / X

/-- **Closed form.**  With `imlog = Im log Γ(1/4 + iX/2)` and the Riemann–Siegel normalization
`θ = imlog - (X/2)·log π`, the average of `σ` over `[0,X]` is `2θ/X`. -/
theorem averagedSymbol_eq {X imlog θ : ℝ} (hX : X ≠ 0)
    (hθ : θ = imlog - X / 2 * Real.log Real.pi) :
    2 / X * imlog - Real.log Real.pi = averagedSymbol θ X := by
  unfold averagedSymbol
  rw [hθ]
  field_simp

/-- **Integrated cubic bound.**  `sinh ℓ - ℓ ≤ (ℓ³/6)·cosh ℓ`, from `cosh t - 1 ≤ (t²/2)cosh t`. -/
theorem sinh_sub_self_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Real.sinh ℓ - ℓ ≤ ℓ ^ (3 : ℕ) / 6 * Real.cosh ℓ := by
  have hmono : MonotoneOn (fun t : ℝ => t ^ (3 : ℕ) / 6 * Real.cosh t - Real.sinh t + t)
      (Set.Ici (0 : ℝ)) := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ (3 : ℕ) / 6 * Real.cosh t - Real.sinh t + t)
        (t ^ (2 : ℕ) / 2 * Real.cosh t + t ^ (3 : ℕ) / 6 * Real.sinh t - Real.cosh t + 1) t := by
      intro t
      have hcube : HasDerivAt (fun t : ℝ => t ^ (3 : ℕ) / 6) (t ^ (2 : ℕ) / 2) t := by
        have h := (hasDerivAt_pow 3 t).div_const 6
        convert! h using 1
        push_cast
        ring
      have h := ((hcube.mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)).add
        (hasDerivAt_id t)
      convert! h using 1
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hkey := cosh_sub_one_le ht0
    have hsinh : (0 : ℝ) ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht0
    have hcube : (0 : ℝ) ≤ t ^ (3 : ℕ) / 6 * Real.sinh t := by positivity
    linarith
  have h0 : (0 : ℝ) ^ (3 : ℕ) / 6 * Real.cosh 0 - Real.sinh 0 + 0 = 0 := by simp
  have := hmono Set.self_mem_Ici hℓ hℓ
  simp only [h0] at this
  linarith [this]

/-- The cutoff `X = π/(2ℓ)` exceeds `t₀` exactly when `ℓ ≤ π/(2t₀)`. -/
theorem cutoff_ge_iff {ℓ t₀ : ℝ} (hℓ : 0 < ℓ) (ht₀ : 0 < t₀) :
    ℓ ≤ Real.pi / (2 * t₀) ↔ t₀ ≤ Real.pi / (2 * ℓ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · intro h
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  · intro h
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h
    linarith

/-- **Positivity criterion at the Riemann–Siegel threshold.**  The elementary baseline is
nonnegative as soon as the averaged symbol `2θ(X)/X` dominates the cubic pole remainder. -/
theorem baseline_nonneg_of_theta {P ℓ X θX : ℝ} (hℓ : 0 ≤ ℓ)
    (hcrit : ℓ ^ (3 : ℕ) / 3 * Real.cosh ℓ ≤ averagedSymbol θX X) :
    0 ≤ 2 * P ^ (2 : ℕ) - 2 * (Real.sinh ℓ - ℓ) + averagedSymbol θX X := by
  have hP : (0 : ℝ) ≤ 2 * P ^ (2 : ℕ) := by positivity
  have hcube := sinh_sub_self_le hℓ
  have hdouble : 2 * (Real.sinh ℓ - ℓ) ≤ ℓ ^ (3 : ℕ) / 3 * Real.cosh ℓ := by linarith
  linarith

/-- Whenever `θ(X) ≥ 0` and the cubic remainder is dominated, the baseline is nonnegative; the sign
of `θ` is therefore what cuts the elementary range off. -/
theorem baseline_nonneg_of_theta_nonneg {P ℓ X θX : ℝ} (hℓ : 0 ≤ ℓ) (_hX : 0 < X)
    (_hθ : 0 ≤ θX) (hsmall : ℓ ^ (3 : ℕ) / 3 * Real.cosh ℓ ≤ 2 * θX / X) :
    0 ≤ 2 * P ^ (2 : ℕ) - 2 * (Real.sinh ℓ - ℓ) + averagedSymbol θX X :=
  baseline_nonneg_of_theta hℓ hsmall

end RHTower
