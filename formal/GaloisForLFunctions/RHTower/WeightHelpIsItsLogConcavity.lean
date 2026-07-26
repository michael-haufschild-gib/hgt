import GaloisForLFunctions.RHTower.FactorialWeightIsOneWay

/-!
# The help the weight gives is exactly its own log-concavity, and it vanishes

The previous entry showed the factorial weight creates hyperbolicity.  This file measures how much,
and finds a clean law.

**The threshold.**  For positive `a, c` the quadratic `a + bX + cX²` is hyperbolic exactly when
`b² ≥ 4ac`.  Weighting the coefficients by `w₀, w₁, w₂ > 0` gives `w₀a + w₁bX + w₂cX²`, hyperbolic
exactly when

```text
b²  ≥  (4 w₀ w₂ / w₁²) · a c .
```

> **The factor by which a weight relaxes the hyperbolicity threshold is precisely `w₁²/(w₀w₂)`, the
> weight's own log-concavity ratio at that place.**

**For the factorial weight.**  With `w_j = 1/(2j)!` centred at index `j`, that ratio is

```text
(2j+3)(2j+4) / ((2j+1)(2j+2)) ,
```

which equals **six** at `j = 0` and tends to **one**.  It is the reciprocal of the window ratio of the
earlier entry, so the two computations agree.

**The creation zone.**  Writing `τ = b²/(ac)`, the weight moves a quadratic from non-hyperbolic to
hyperbolic exactly when `τ` lies in

```text
[ 4·(2j+1)(2j+2)/((2j+3)(2j+4)) ,  4 ) ,
```

an interval of length `4(1 - windowRatio)`, which is `10/3` at the bottom and shrinks like `1/j`.

> **The weight's help is large where the index is small and vanishes at infinity.  The hypothesis
> needs the help at every index, and the help available is `1 + O(1/j)`.**

This file formalizes the weighted threshold law, the identification of the relaxation factor with the
weight's log-concavity ratio, its value six at the bottom, the creation zone and its shrinking.
-/

open Real

noncomputable section

namespace RHTower

/-- **The weighted threshold law.**  A weighted quadratic with positive outer weights is hyperbolic
exactly when the middle coefficient squared clears `4w₀w₂/w₁²` times the outer product. -/
theorem weighted_threshold (a b c w₀ w₁ w₂ : ℝ) :
    0 ≤ (w₁ * b) ^ 2 - 4 * (w₀ * a) * (w₂ * c) ↔ 4 * w₀ * w₂ * (a * c) ≤ w₁ ^ 2 * b ^ 2 := by
  constructor <;> intro h <;> nlinarith [h]

/-- The relaxation factor of a weight at a place: its log-concavity ratio. -/
def weightRatio (j : ℕ) : ℝ :=
  ((2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 4)) / ((2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2))

/-- **At the bottom the weight gives a factor six.** -/
theorem weightRatio_zero : weightRatio 0 = 6 := by
  unfold weightRatio
  norm_num

theorem weightRatio_pos (j : ℕ) : 0 < weightRatio j := by
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold weightRatio
  positivity

/-- **The relaxation factor exceeds one at every place**: the weight always helps, never hurts. -/
theorem one_lt_weightRatio (j : ℕ) : 1 < weightRatio j := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold weightRatio
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- **It is the reciprocal of the window ratio.**  The two computations of the previous entries agree
term by term. -/
theorem weightRatio_eq_inv_windowRatio (j : ℕ) :
    weightRatio j = 1 / windowRatio (2 * j) := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold weightRatio windowRatio
  rw [one_div_div]
  push_cast
  ring

/-- The lower end of the creation zone: below `4` exactly because the weight helps. -/
theorem creation_zone_lower_lt_four (j : ℕ) : 4 / weightRatio j < 4 := by
  have h1 := one_lt_weightRatio j
  have h0 := weightRatio_pos j
  rw [div_lt_iff₀ h0]
  nlinarith

/-- **The creation zone is nonempty at every place.** -/
theorem creation_zone_nonempty (j : ℕ) : ∃ τ : ℝ, 4 / weightRatio j ≤ τ ∧ τ < 4 :=
  ⟨4 / weightRatio j, le_refl _, creation_zone_lower_lt_four j⟩

/-- **At the bottom the zone is `[2/3, 4)`,** of length `10/3`. -/
theorem creation_zone_zero : 4 / weightRatio 0 = 2 / 3 := by
  rw [weightRatio_zero]
  norm_num

/-- **The zone shrinks.**  Its length is `4(1 - 1/weightRatio)`, which tends to zero because the
window ratio tends to one. -/
theorem creation_zone_length (j : ℕ) :
    4 - 4 / weightRatio j = 4 * (1 - windowRatio (2 * j)) := by
  rw [weightRatio_eq_inv_windowRatio, div_div_eq_mul_div, div_one]
  ring

end RHTower
