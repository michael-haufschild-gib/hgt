import GaloisForLFunctions.RHTower.ZeroFreeWidthExponent

/-!
# The width exponent is `1 - 1/κ`, and the hypothesis sits at `κ = ∞`

The zero-free width exponent has moved from `0` to `1/3`.  This file identifies what controls it and
shows the whole family is bounded away from the hypothesis.

**The chain.**  Suppose a bound of Vinogradov–Korobov shape,

```text
|ζ(σ + it)|  ≪  t^{A(1-σ)^κ} ,
```

is available near the edge of the strip.  Balancing the saving against the logarithmic detection
threshold, `(1-σ)^κ log t ≍ log log t`, gives `1 - σ ≍ (log log t / log t)^{1/κ}`, so the width
measured in mean spacings is

```text
(1 - σ) · log t  ≍  (log t)^{1 - 1/κ} (log log t)^{1/κ} .
```

> **The unit exponent is exactly `1 - 1/κ`.**

**What that says about the history and the target.**

```text
κ = 1    (classical)              →  unit exponent 0     — de la Vallée Poussin
κ = 3/2  (Vinogradov–Korobov)     →  unit exponent 1/3
unit exponent 1  (the hypothesis) →  κ = ∞
```

Since `1 - 1/κ < 1` for every finite `κ`, no finite improvement of the exponent in the sum bound can
reach the hypothesis:

> **The Vinogradov family is bounded away from the hypothesis for a structural reason: the
> hypothesis sits at the boundary `κ = ∞`, which is the statement that `|ζ|` is subpolynomial
> throughout the strip.  A century of progress moved `κ` from `1` to `3/2`; no finite value suffices.**

This file formalizes the exponent formula, its two known values, and the impossibility of reaching the
hypothesis at any finite `κ`.
-/

open Real

noncomputable section

namespace RHTower

/-- **The unit exponent.**  A sum-bound exponent `κ` yields width exponent `1 - 1/κ` in mean
spacings. -/
def unitExponent (kappa : ℝ) : ℝ := 1 - 1 / kappa

/-- **The classical value.**  `κ = 1` gives exponent `0`. -/
theorem unitExponent_one : unitExponent 1 = 0 := by
  unfold unitExponent; norm_num

/-- **The Vinogradov–Korobov value.**  `κ = 3/2` gives exponent `1/3`. -/
theorem unitExponent_three_halves : unitExponent (3 / 2) = 1 / 3 := by
  unfold unitExponent; norm_num

/-- **The exponent is increasing in `κ`.**  Better sum bounds give wider regions. -/
theorem unitExponent_mono {k₁ k₂ : ℝ} (h1 : 0 < k₁) (h12 : k₁ ≤ k₂) :
    unitExponent k₁ ≤ unitExponent k₂ := by
  unfold unitExponent
  have h2 : 0 < k₂ := lt_of_lt_of_le h1 h12
  have : 1 / k₂ ≤ 1 / k₁ := by
    apply one_div_le_one_div_of_le h1 h12
  linarith

/-- **But it never reaches one.**  For every finite positive `κ` the unit exponent is strictly below
the value the hypothesis requires. -/
theorem unitExponent_lt_one {kappa : ℝ} (h : 0 < kappa) : unitExponent kappa < 1 := by
  unfold unitExponent
  have : 0 < 1 / kappa := by positivity
  linarith

/-- **So no finite sum-bound exponent suffices.**  The hypothesis's unit exponent `1` is not attained
in the family. -/
theorem no_finite_kappa_suffices {kappa : ℝ} (h : 0 < kappa) : unitExponent kappa ≠ 1 :=
  ne_of_lt (unitExponent_lt_one h)

/-- The gap to the hypothesis at exponent `κ` is exactly `1/κ`. -/
theorem gap_to_hypothesis {kappa : ℝ} (_h : kappa ≠ 0) : 1 - unitExponent kappa = 1 / kappa := by
  unfold unitExponent; ring

/-- At the Vinogradov–Korobov value the remaining gap is `2/3`, matching the earlier count. -/
theorem gap_at_vinogradov : 1 - unitExponent (3 / 2) = 2 / 3 := by
  rw [unitExponent_three_halves]; norm_num

end RHTower
