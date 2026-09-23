import GaloisForLFunctions.RHTower.OverlapLocalizedPrimeTerm

/-!
# The archimedean term rewards concentration

The archimedean part of the Weil functional is

```text
A(h) = (1/2π) ∫ |ĥ(ξ)|² σ(ξ) dξ ,     σ(ξ) = Re Ψ(1/4 + iξ/2) - log π ,
```

and `σ` is **increasing in `|ξ|`**: from `Ψ(z) = -γ + Σ_{k≥0}(1/(k+1) - 1/(k+z))`,

```text
Re Ψ(a + ib) = -γ + Σ_{k≥0} ( 1/(k+1) - (k+a)/((k+a)² + b²) ),
```

and every summand increases with `b²` because `c/(c² + b²)` decreases.  So `σ(ξ) ≥ σ(0)` always, and
`σ(ξ) ≍ log(|ξ|/2π)` grows without bound.  Splitting the frequency line at `Ξ` therefore gives

```text
A(h) ≥ σ(0)‖h‖² + β · ( σ(Ξ) - σ(0) ) ,     β = high-frequency mass fraction beyond Ξ.
```

The uncertainty step converts concentration into high-frequency mass.  If `h` carries mass
`μ = ‖h‖²_{L²(E)}` on a set `E` of measure `m`, then the low-pass part obeys
`‖P_Ξ h‖_∞ ≤ √(Ξ/π)‖h‖`, so `‖P_Ξ h‖_{L²(E)} ≤ √(mΞ/π)‖h‖` and the triangle inequality gives

```text
√μ ≤ √(mΞ/π) + √β .
```

Choosing `Ξ = πμ/(4m)` makes the first term `√μ/2`, whence `β ≥ μ/4`.  Therefore

```text
A(h) ≥ σ(0)‖h‖² + (μ/4)·( σ(πμ/(4m)) - σ(0) ) ,
```

and since `σ(πμ/(4m)) ≍ log(μ/(8m))`, the gain over the universal minimum grows like
`(μ/4)·log(μ/(8m))` as the concentration set shrinks.

Paired with the overlap localization of the previous module — the first prime past the
Connes–Consani threshold costs at most `(log 2/√2)·μ` on a set of measure `2η` — the archimedean
gain covers the prime cost as soon as `(1/4)log(μ/(16η)) ≥ log 2/√2`, that is `μ ≳ 114 η`; and when
`μ ≲ 114 η` the prime cost is itself `O(η)`.  Either way the prime term past the threshold is
dominated by the archimedean reward except on an `O(η)` remainder.

This file formalizes the three ingredients: monotonicity of the digamma summand in the ordinate, the
two-band lower bound, and the uncertainty step with its explicit choice of cutoff.
-/

open Real

noncomputable section

namespace RHTower

/-- **Monotonicity of the digamma summand.**  Each term `-(c/(c²+b²))` of the series for
`Re Ψ(a+ib)` increases with `b²`, so `σ` increases with `|ξ|`. -/
theorem digamma_summand_mono {c b₁ b₂ : ℝ} (hc : 0 < c) (h : b₁ ^ (2 : ℕ) ≤ b₂ ^ (2 : ℕ)) :
    -(c / (c ^ (2 : ℕ) + b₁ ^ (2 : ℕ))) ≤ -(c / (c ^ (2 : ℕ) + b₂ ^ (2 : ℕ))) := by
  have h1 : (0 : ℝ) < c ^ (2 : ℕ) + b₁ ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) < c ^ (2 : ℕ) + b₂ ^ (2 : ℕ) := by positivity
  have hmono : c / (c ^ (2 : ℕ) + b₂ ^ (2 : ℕ)) ≤ c / (c ^ (2 : ℕ) + b₁ ^ (2 : ℕ)) := by
    apply div_le_div_of_nonneg_left hc.le h1
    linarith
  linarith

/-- **Two-band lower bound.**  With the symbol at least `σ₀` everywhere and at least `σ_Ξ` beyond the
cutoff, the weighted average exceeds `σ₀` by the high-frequency fraction times the increment. -/
theorem two_band_lower {σ₀ σΞ β A : ℝ} (_hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1) (_hmono : σ₀ ≤ σΞ)
    (hA : σ₀ * (1 - β) + σΞ * β ≤ A) :
    σ₀ + β * (σΞ - σ₀) ≤ A := by
  have : σ₀ * (1 - β) + σΞ * β = σ₀ + β * (σΞ - σ₀) := by ring
  linarith [this ▸ hA]

/-- **The uncertainty step.**  If the mass on a set of measure `m` is `μ` and the low-pass part
contributes at most `√(mΞ/π)`, then choosing the cutoff `Ξ = πμ/(4m)` forces the high-frequency
fraction to be at least `μ/4`. -/
theorem highFreq_mass_ge {μ m Ξ β : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) (hβ : 0 ≤ β)
    (hΞ : Ξ = Real.pi * μ / (4 * m))
    (hsplit : Real.sqrt μ ≤ Real.sqrt (m * Ξ / Real.pi) + Real.sqrt β) :
    μ / 4 ≤ β := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hval : m * Ξ / Real.pi = μ / 4 := by
    rw [hΞ]
    field_simp
  rw [hval] at hsplit
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hquarter : Real.sqrt (μ / 4) = Real.sqrt μ / 2 := by
    rw [Real.sqrt_div hμ, h4]
  rw [hquarter] at hsplit
  have hhalf : Real.sqrt μ / 2 ≤ Real.sqrt β := by linarith
  have hsq : (Real.sqrt μ / 2) ^ (2 : ℕ) ≤ (Real.sqrt β) ^ (2 : ℕ) := by
    have h0 : (0 : ℝ) ≤ Real.sqrt μ / 2 := by positivity
    nlinarith [hhalf, h0]
  rw [Real.sq_sqrt hβ] at hsq
  have hμsq : (Real.sqrt μ) ^ (2 : ℕ) = μ := Real.sq_sqrt hμ
  have : (Real.sqrt μ / 2) ^ (2 : ℕ) = μ / 4 := by
    rw [div_pow, hμsq]; norm_num
  linarith [this ▸ hsq]

/-- **Assembled gain.**  Concentration of mass `μ` on a set of measure `m` forces the archimedean
term above its universal minimum by at least `(μ/4)(σ_Ξ - σ₀)` at the cutoff `Ξ = πμ/(4m)`. -/
theorem archimedean_gain {σ₀ σΞ μ m β A : ℝ} (_hμ : 0 ≤ μ) (_hm : 0 < m) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hmono : σ₀ ≤ σΞ)
    (hmass : μ / 4 ≤ β)
    (hA : σ₀ * (1 - β) + σΞ * β ≤ A) :
    σ₀ + (μ / 4) * (σΞ - σ₀) ≤ A := by
  have hband := two_band_lower hβ0 hβ1 hmono hA
  have hstep : (μ / 4) * (σΞ - σ₀) ≤ β * (σΞ - σ₀) :=
    mul_le_mul_of_nonneg_right hmass (by linarith)
  linarith

/-- The break-even threshold: the archimedean gain covers the damped first-prime cost as soon as the
symbol increment exceeds `4 log 2/√2`. -/
theorem breakEven {σ₀ σΞ μ : ℝ} (hμ : 0 ≤ μ)
    (hgain : 4 * (Real.log 2 / Real.sqrt 2) ≤ σΞ - σ₀) :
    (Real.log 2 / Real.sqrt 2) * μ ≤ (μ / 4) * (σΞ - σ₀) := by
  nlinarith [hgain, hμ]

end RHTower
