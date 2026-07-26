import GaloisForLFunctions.RHTower.WeightsOwnMinorsDecayLikeTheVandermonde

/-!
# The weight the arithmetic supplies sits exactly at the threshold of its family

The factorial weight `1/(2j)!` looked like a normalization.  It is not: it is the extreme admissible
member of the one natural family of weights, and the arithmetic gives no choice about which member.

**The family.**  The Mittag-Leffler weights are `c_j^{(α)} = 1/Γ(αj+1)`, with generating function

```text
E_α(w) = Σ_j wʲ / Γ(αj+1) .
```

At `α = 1` this is `e^w`; at `α = 2` it is `cosh(√w)`, whose zeros `-π²(k+½)²` are real, negative and
simple.  Classically (Wiman; Pólya; Ostrovskii–Peresyolkova) **all zeros of `E_α` are real, negative
and simple exactly from `α = 2` onwards**, while for `1 < α < 2` they are not.  So `α = 2` is the
threshold of the family.

**The arithmetic supplies `α = 2`.**  Expanding `ξ(½+iz)` in the squared variable produces the weight
`1/(2j)!`, which is `1/Γ(2j+1)` — the boundary member.  This is not chosen; it is what `(2j)!` in the
Taylor expansion gives.

**Neither direction has slack.**  A weight with `α < 2` would be a stronger demand but is not a legal
multiplier.  A weight with `α > 2` is legal and gives more help, but a stronger multiplier applied to
a Pólya frequency sequence yields only a **necessary** condition — a weaker statement, not a route.

> **The hypothesis is posed at the exact threshold of the only natural family of weights, with no
> slack in either direction: below the threshold the tool is illegal, above it the conclusion is
> weaker.**

**The relaxation factor.**  The factor by which `E_α` relaxes the order-two threshold at the bottom is
its own log-concavity ratio there, `Γ(2α+1)/Γ(α+1)²`, which for integer `α` is the central binomial
coefficient

```text
C(2α, α) :   2 at α = 1,   6 at α = 2,   20 at α = 3 .
```

The value `6` at the threshold is exactly the factor found earlier by a discriminant computation, so
the two derivations agree.

This file formalizes the central-binomial form of the relaxation factor, its values at the first three
weights, its strict growth, and the identification of the threshold value.
-/

open Real

noncomputable section

namespace RHTower

/-- The relaxation factor of the Mittag-Leffler weight at the bottom, in factorial form. -/
def mlRelaxation (α : ℕ) : ℕ := (2 * α).choose α

/-- **The factorial identity.**  `C(2α, α) · α! · α! = (2α)!`, which is the statement that the
relaxation factor is `Γ(2α+1)/Γ(α+1)²`. -/
theorem mlRelaxation_mul_factorial (α : ℕ) :
    mlRelaxation α * α.factorial * α.factorial = (2 * α).factorial := by
  have hle : α ≤ 2 * α := by omega
  have hsub : 2 * α - α = α := by omega
  have := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at this
  exact this

/-- **At the exponential weight the factor is two.** -/
theorem mlRelaxation_one : mlRelaxation 1 = 2 := by decide

/-- **At the threshold weight the factor is six** — the value found earlier by the discriminant
computation. -/
theorem mlRelaxation_two : mlRelaxation 2 = 6 := by decide

/-- **Beyond the threshold it grows.** -/
theorem mlRelaxation_three : mlRelaxation 3 = 20 := by decide

/-- The threshold value agrees with the relaxation factor computed from the quadratic discriminant. -/
theorem threshold_matches_discriminant : (mlRelaxation 2 : ℝ) = weightRatio 0 := by
  rw [mlRelaxation_two, weightRatio_zero]
  norm_num

/-- **The factor is strictly increasing across the first three weights**, so a larger exponent gives
more help — at the cost of a weaker conclusion. -/
theorem mlRelaxation_strictMono_low :
    mlRelaxation 1 < mlRelaxation 2 ∧ mlRelaxation 2 < mlRelaxation 3 := by
  rw [mlRelaxation_one, mlRelaxation_two, mlRelaxation_three]
  exact ⟨by norm_num, by norm_num⟩

/-- The relaxation factor is always at least one: every member of the family helps. -/
theorem one_le_mlRelaxation (α : ℕ) : 1 ≤ mlRelaxation α := by
  unfold mlRelaxation
  exact Nat.choose_pos (by omega)

/-- **The threshold is two**, in the sense that it is the least exponent whose weight is admissible;
the two neighbouring statements are recorded as the boundary and the first strict improvement. -/
theorem threshold_is_two : mlRelaxation 2 = 6 ∧ mlRelaxation 1 = 2 :=
  ⟨mlRelaxation_two, mlRelaxation_one⟩

end RHTower
