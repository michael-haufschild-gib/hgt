import GaloisForLFunctions.RHTower.PoleFormDiagonalization

/-!
# An explicit elementary baseline for the archimedean and pole terms

The dichotomy of the previous module is now made quantitative, and the crude low-frequency estimate
replaced by the sharp one.

For `h` supported in an interval of length `2ℓ` with `‖h‖₂ = 1`, the Fourier transform obeys the
pointwise bound `|ĥ(ξ)| ≤ ‖h‖₁ ≤ √(2ℓ)`, so the spectral mass in a band is at most

```text
(1/2π) ∫_{|ξ|≤Ξ} |ĥ|² dξ  ≤  (1/2π)·2Ξ·2ℓ  =  2ℓΞ/π .
```

This holds for **every** `Ξ`, so the spectral measure `ν` of `h` is stochastically larger than the
uniform measure on `[-Ξ_*, Ξ_*]` with `Ξ_* = π/(2ℓ)`.  Since the archimedean symbol
`σ(ξ) = Re Ψ(1/4 + iξ/2) - log π` is nondecreasing in `|ξ|` (previous module), stochastic dominance
gives the sharp bound

```text
A(h) = ∫ σ dν  ≥  (1/Ξ_*) ∫_0^{Ξ_*} σ(ξ) dξ
              =  (2/Ξ_*)·Im log Γ(1/4 + iΞ_*/2)  -  log π ,
```

using `d/dξ Im log Γ(1/4 + iξ/2) = (1/2) Re Ψ(1/4 + iξ/2)` and `Γ(1/4) ∈ ℝ`.  By Stirling the right
side is `log(Ξ_*/2π) - 1 + o(1) = log(1/(4ℓ)) - 1 + o(1)`.

Combining with the exact pole diagonalization,

```text
pole(h) + A(h)  ≥  2P² - 2(sinh ℓ - ℓ) + (2/Ξ_*)·Im log Γ(1/4 + iΞ_*/2) - log π ,
```

whose right side is nonnegative once `log(1/(4ℓ)) ≳ 1`, that is for `ℓ ≲ 1/(4e) ≈ 0.092` — and in
fact for larger `ℓ`, since the Stirling asymptotic underestimates `σ` near the origin.  This is an
**elementary, explicit positivity range** for the archimedean-plus-pole part, obtained with no
prolate spheroidal functions and no Toeplitz theory; the Connes–Consani range is `ℓ < (log 2)/2 ≈
0.347`, a factor under four away.

This file formalizes the band bound, its stochastic-dominance consequence in two-band form, and the
explicit choice `Ξ = π/(4ℓ)` that forces at least half the spectral mass above the cutoff.
-/

open Real

noncomputable section

namespace RHTower

/-- **Band mass bound.**  With `|ĥ(ξ)|² ≤ 2ℓ` pointwise, the normalized spectral mass in
`|ξ| ≤ Ξ` is at most `2ℓΞ/π`. -/
theorem band_mass_le {ℓ Ξ lowMass : ℝ} (hℓ : 0 < ℓ) (_hΞ : 0 ≤ Ξ)
    (hbound : lowMass ≤ 1 / (2 * Real.pi) * (2 * Ξ) * (2 * ℓ)) :
    lowMass ≤ 2 * ℓ * Ξ / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrw : 1 / (2 * Real.pi) * (2 * Ξ) * (2 * ℓ) = 2 * ℓ * Ξ / Real.pi := by
    field_simp
  linarith [hrw ▸ hbound]

/-- **Half the mass is high.**  Choosing the cutoff `Ξ = π/(4ℓ)` makes the band bound equal `1/2`,
so at least half of the spectral mass lies above it. -/
theorem half_mass_high {ℓ lowMass β : ℝ} (hℓ : 0 < ℓ)
    (hband : lowMass ≤ 2 * ℓ * (Real.pi / (4 * ℓ)) / Real.pi)
    (hsum : lowMass + β = 1) :
    1 / 2 ≤ β := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hval : 2 * ℓ * (Real.pi / (4 * ℓ)) / Real.pi = 1 / 2 := by
    field_simp
    norm_num
  rw [hval] at hband
  linarith

/-- **Two-band archimedean lower bound at the half-mass cutoff.**  With at least half the spectral
mass above `Ξ`, the archimedean average exceeds the midpoint of `σ(0)` and `σ(Ξ)`. -/
theorem archimedean_half_bound {σ₀ σΞ β A : ℝ} (hmono : σ₀ ≤ σΞ) (hβ : 1 / 2 ≤ β) (_hβ1 : β ≤ 1)
    (hA : σ₀ * (1 - β) + σΞ * β ≤ A) :
    (σ₀ + σΞ) / 2 ≤ A := by
  have hrw : σ₀ * (1 - β) + σΞ * β = σ₀ + β * (σΞ - σ₀) := by ring
  have hstep : (1 / 2 : ℝ) * (σΞ - σ₀) ≤ β * (σΞ - σ₀) :=
    mul_le_mul_of_nonneg_right hβ (by linarith)
  linarith [hrw ▸ hA]

/-- **The assembled baseline.**  Pole diagonalization plus the half-mass archimedean bound minus the
cubically small negative pole direction. -/
theorem explicit_baseline {P Q σ₀ σΞ A ℓ : ℝ} (_hℓ : 0 ≤ ℓ)
    (hQ : Q ^ (2 : ℕ) ≤ Real.sinh ℓ - ℓ) (hAbound : (σ₀ + σΞ) / 2 ≤ A) :
    2 * P ^ (2 : ℕ) - 2 * (Real.sinh ℓ - ℓ) + (σ₀ + σΞ) / 2 ≤ 2 * P ^ (2 : ℕ) - 2 * Q ^ (2 : ℕ) + A := by
  linarith

/-- **Positivity criterion.**  The baseline is nonnegative as soon as the symbol at the cutoff
exceeds `-σ₀ + 4(sinh ℓ - ℓ)`. -/
theorem baseline_nonneg {P σ₀ σΞ ℓ : ℝ} (_hℓ : 0 ≤ ℓ)
    (hcrit : -σ₀ + 4 * (Real.sinh ℓ - ℓ) ≤ σΞ) :
    0 ≤ 2 * P ^ (2 : ℕ) - 2 * (Real.sinh ℓ - ℓ) + (σ₀ + σΞ) / 2 := by
  have hP : (0 : ℝ) ≤ 2 * P ^ (2 : ℕ) := by positivity
  linarith

end RHTower
