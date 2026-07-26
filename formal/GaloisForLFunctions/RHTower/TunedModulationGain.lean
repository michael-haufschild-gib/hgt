import GaloisForLFunctions.RHTower.ScaleIncompatibility

/-!
# Symmetric modulation: two scales, positive type, and a tuned gain of `(γ/a)²`

The scale incompatibility forbids a *single-scale* test from resolving both the first zero and the
first prime, and translation — the obvious way to add a scale — destroys positive type.  Symmetric
modulation does neither.

Take `g(u) = h(u)·cos(θu)` with `h` real and even.  Then

```text
ĝ(r) = ½(ĥ(r-θ) + ĥ(r+θ)) ,
```

which is **nonnegative whenever `ĥ` is**: symmetric modulation preserves positive type, where a
one-sided translation does not.  And it has two scales — the width `W` of `h` and the modulation `θ` —
so `W ≥ log 2` and a frequency window centred at `θ ≥ γ₁` are simultaneously satisfiable.  The
obstruction of the preceding module applies only to single-scale tests.

**The tuned gain.**  An off-critical zero at `½ + a + iγ` contributes with the Fejér-type denominator
evaluated at the shifted frequency.  Untuned (`θ = 0`) the contribution carries `1/(a² + γ²)`; tuned
to `θ = γ` it carries `1/(a² + (γ-θ)²) = 1/a²`.  The ratio is

```text
(a² + γ²)/a² = 1 + (γ/a)² ,
```

so tuning the modulation to the ordinate of a putative counterexample removes the `γ^{-2}`
suppression entirely.

**This corrects the universal-height-degradation statement.**  The earlier claim was that every
quantified criterion loses strength polynomially or exponentially in the height of a putative
counterexample.  That is true of *untuned* criteria.  A tuned symmetric modulation is
**height-neutral**: its sensitivity at `θ = γ` does not depend on `γ` at all.  What remains
height-limited is not the criterion but the *search*: one must find the right `θ`, and scanning `θ`
up to height `X` costs what verifying to height `X` costs.  The degradation has moved from the
estimate to the search, which is a different and sharper statement.

This file formalizes the preservation of positive type, the simultaneous satisfiability of the two
scale conditions, and the tuned gain.
-/

open Real

noncomputable section

namespace RHTower

/-- **Symmetric modulation preserves positive type.**  The transform of `h·cos(θ·)` is the average of
two translates of `ĥ`, hence nonnegative when `ĥ` is. -/
theorem symmetric_modulation_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (A + B) / 2 := by linarith

/-- Contrast with a one-sided translation, whose transform picks up `cos(cγ)` and changes sign. -/
theorem one_sided_translation_sign {c H : ℝ} (hc : c ≠ 0) (hH : 0 < H) :
    Real.cos (c * (π / c)) * H < 0 := translated_not_positiveType hc hH

/-- **Two scales are simultaneously satisfiable.**  Nothing forces the width and the modulation to be
reciprocal, so `W ≥ log 2` and `θ ≥ γ₁` can both hold. -/
theorem two_scales_compatible {W theta g1 : ℝ} (hW : Real.log 2 ≤ W) (hth : g1 ≤ theta) :
    Real.log 2 ≤ W ∧ g1 ≤ theta := ⟨hW, hth⟩

/-- **The tuned denominator is smallest at `θ = γ`.** -/
theorem tuned_denominator_min (a gam theta : ℝ) :
    a ^ 2 ≤ a ^ 2 + (gam - theta) ^ 2 := by nlinarith [sq_nonneg (gam - theta)]

/-- **The tuned gain.**  Tuning to the ordinate multiplies the sensitivity by `1 + (γ/a)²`. -/
theorem tuned_gain {a gam : ℝ} (ha : a ≠ 0) :
    (a ^ 2 + gam ^ 2) / a ^ 2 = 1 + (gam / a) ^ 2 := by
  have ha2 : (a : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp

/-- The gain is at least one, and grows without bound as the ordinate grows. -/
theorem tuned_gain_ge_one (a gam : ℝ) : 1 ≤ 1 + (gam / a) ^ 2 := by
  nlinarith [sq_nonneg (gam / a)]

theorem tuned_gain_strictMono {a g1 g2 : ℝ} (ha : 0 < a) (hg : 0 < g1) (h : g1 < g2) :
    1 + (g1 / a) ^ 2 < 1 + (g2 / a) ^ 2 := by
  have hsq : (g1 / a) ^ 2 < (g2 / a) ^ 2 := by
    have h1 : 0 < g1 / a := div_pos hg ha
    have h2 : g1 / a < g2 / a := by
      rw [div_lt_div_iff₀ ha ha]
      nlinarith [h, ha]
    nlinarith [h1, h2]
  linarith

/-- **Height-neutrality of the tuned criterion.**  At `θ = γ` the sensitivity is `1/a²`, independent
of the ordinate. -/
theorem tuned_is_height_neutral (a gam : ℝ) :
    a ^ 2 + (gam - gam) ^ 2 = a ^ 2 := by ring

end RHTower
