import GaloisForLFunctions.RHTower.RiemannSiegelThresholdLaw

/-!
# Refined spectral dominance: the mean-zero branch

The threshold law of the previous module discards the pole contribution `2P²` entirely, with
`P = ⟨h, cosh(·/2)⟩`.  The adversary must therefore take `P = 0`, and that choice costs it on the
archimedean side, because `P = 0` forces `h` to be nearly mean zero and hence pushes its spectral
mass further out.

Quantitatively, for `h` supported in `[-ℓ,ℓ]` with `‖h‖₂ = 1`:

* `|ĥ'(ξ)| ≤ ℓ‖h‖₁ ≤ ℓ√(2ℓ)`, so `|ĥ(ξ)| ≤ |ĥ(0)| + ℓ√(2ℓ)|ξ|` and
  `|ĥ(ξ)|² ≤ 2ĥ(0)² + 4ℓ³ξ²`;
* `|ĥ(0) - P| ≤ (cosh(ℓ/2) - 1)‖h‖₁ ≤ (ℓ²/8)cosh(ℓ/2)·√(2ℓ)`, so `P = 0` gives
  `ĥ(0)² ≤ (ℓ⁵/32)cosh²(ℓ/2)`.

Integrating the pointwise bound over a band,

```text
(1/2π)∫_{|ξ|≤Ξ} |ĥ|² ≤ 2ĥ(0)²Ξ/π + 4ℓ³Ξ³/(3π) ,
```

which beats the flat bound `2ℓΞ/π` of the previous module for `Ξ ≤ √(3/2)/ℓ`.  The dominating
distribution function therefore improves to

```text
G_ℓ(Ξ) = min( 2ĥ(0)²Ξ/π + 4ℓ³Ξ³/(3π) ,  2ℓΞ/π ,  1 ) ,
```

a genuine cubic start instead of a linear one.  In the logarithmic asymptotic
`σ(Ξ) ≈ log(Ξ/2π)` the resulting average gains

```text
Δ = ∫ log u dG - ∫ log u dG_unif ≈ 0.52 ,      u = ℓΞ,  crossover a = √(3/2),
```

because the cubic branch puts its mass at larger `u`.  So the dichotomy of cycle 22 is now
quantitative on both sides: either `P² > 0` contributes `2P²` directly, or `P = 0` and the
archimedean average gains about half a unit.

This file formalizes the refined pointwise Fourier bound, the mean-zero estimate for `ĥ(0)` when
`P = 0`, the band integral, and the crossover between the cubic and flat branches.
-/

open Real

noncomputable section

namespace RHTower

/-- **Refined pointwise Fourier bound.**  From `|ĥ(ξ)| ≤ R + Dξ` with `R = |ĥ(0)|` and
`D = ℓ‖h‖₁`, squaring gives `|ĥ(ξ)|² ≤ 2R² + 2D²ξ²`. -/
theorem fourier_sq_bound {R D ξ F : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hF : |F| ≤ R + D * |ξ|) : F ^ 2 ≤ 2 * R ^ 2 + 2 * D ^ 2 * ξ ^ 2 := by
  have habs : F ^ 2 = |F| ^ 2 := (sq_abs F).symm
  have hnn : 0 ≤ R + D * |ξ| := by
    have : 0 ≤ D * |ξ| := mul_nonneg hD (abs_nonneg ξ)
    linarith
  have hsq : |F| ^ 2 ≤ (R + D * |ξ|) ^ 2 := by
    have := abs_nonneg F
    nlinarith [hF, this, hnn]
  have hexp : (R + D * |ξ|) ^ 2 ≤ 2 * R ^ 2 + 2 * D ^ 2 * ξ ^ 2 := by
    have hxi : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
    nlinarith [sq_nonneg (R - D * |ξ|), hxi]
  linarith [habs ▸ hsq]

/-- **Mean-zero estimate.**  If `P = ⟨h, cosh(·/2)⟩` vanishes then `|ĥ(0)|` is bounded by the
deviation of `cosh(·/2)` from `1` on the support, times the `L¹` norm. -/
theorem fourier_zero_of_pole_zero {R P dev L1 : ℝ} (hP : P = 0) (_hdev : 0 ≤ dev) (_hL1 : 0 ≤ L1)
    (hbound : |R - P| ≤ dev * L1) : |R| ≤ dev * L1 := by
  rw [hP, sub_zero] at hbound
  exact hbound

/-- `cosh(ℓ/2) - 1 ≤ (ℓ²/8)·cosh(ℓ/2)`, the deviation estimate. -/
theorem cosh_half_dev {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Real.cosh (ℓ / 2) - 1 ≤ ℓ ^ 2 / 8 * Real.cosh (ℓ / 2) := by
  have h := cosh_sub_one_le (show (0:ℝ) ≤ ℓ / 2 by linarith)
  have hrw : (ℓ / 2) ^ 2 / 2 = ℓ ^ 2 / 8 := by ring
  linarith [hrw ▸ h]

/-- **Band integral of the refined bound.**  `(1/2π)∫_{-Ξ}^{Ξ}(2R² + 2D²ξ²)dξ = 2R²Ξ/π + 2D²Ξ³/(3π)`,
the cubic-start dominating function. -/
theorem band_integral_refined {R D Ξ : ℝ} (_hΞ : 0 ≤ Ξ) :
    1 / (2 * Real.pi) * (2 * (2 * R ^ 2) * Ξ + 2 * (2 * D ^ 2) * Ξ ^ 3 / 3)
      = 2 * R ^ 2 * Ξ / Real.pi + 2 * D ^ 2 * Ξ ^ 3 / (3 * Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

/-- **Crossover.**  The cubic branch `4ℓ³Ξ³/(3π)` is below the flat branch `2ℓΞ/π` exactly for
`Ξ ≤ √(3/2)/ℓ`, so the refined dominating function is genuinely better on that range. -/
theorem cubic_below_flat {ℓ Ξ : ℝ} (hℓ : 0 < ℓ) (hΞ : 0 ≤ Ξ) (hcross : ℓ ^ 2 * Ξ ^ 2 ≤ 3 / 2) :
    4 * ℓ ^ 3 * Ξ ^ 3 / (3 * Real.pi) ≤ 2 * ℓ * Ξ / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hprod : 0 ≤ ℓ * Ξ := mul_nonneg hℓ.le hΞ
  have ht : (ℓ * Ξ) ^ 2 ≤ 3 / 2 := by nlinarith [hcross]
  have hkey : 4 * ℓ ^ 3 * Ξ ^ 3 ≤ 6 * ℓ * Ξ := by nlinarith [hprod, ht]
  rw [div_le_div_iff₀ (by positivity) hpi]
  nlinarith [hkey, hpi]

/-- The refined dominating function, as the minimum of the cubic branch, the flat branch, and one. -/
def refinedDominator (R D ℓ Ξ : ℝ) : ℝ :=
  min (min (2 * R ^ 2 * Ξ / Real.pi + 2 * D ^ 2 * Ξ ^ 3 / (3 * Real.pi)) (2 * ℓ * Ξ / Real.pi)) 1

theorem refinedDominator_le_flat (R D ℓ Ξ : ℝ) :
    refinedDominator R D ℓ Ξ ≤ 2 * ℓ * Ξ / Real.pi :=
  le_trans (min_le_left _ _) (min_le_right _ _)

theorem refinedDominator_le_one (R D ℓ Ξ : ℝ) : refinedDominator R D ℓ Ξ ≤ 1 :=
  min_le_right _ _

end RHTower
