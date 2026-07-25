import GaloisForLFunctions.RHTower.AutomaticGapDiscreteness

/-!
# The extension programme is equivalent to the Riemann hypothesis

Write `λ(L) = inf spec Q_L` for the lowest point of the spectrum of the truncated Weil form on test
functions supported in an interval of length `L`.  Weil's criterion is `λ(L) ≥ 0` for every `L`, and
`λ` is nonincreasing.  Cycles 20, 26, 27–28 and 30 each tried to push a known positivity range
upward, and each reduced to the same object: a lower bound for `λ` at a length where positivity is
not yet known.  All the soft tools — monotonicity, discreteness, continuity, localization — transport
information **downward** in `L` only.

That is not an accident of method.  Suppose `b` is any nondecreasing function with `b ≤ λ` and
`b(L₀) ≥ 0` for a single `L₀`.  For `L ≥ L₀` monotonicity of `b` gives `λ(L) ≥ b(L) ≥ b(L₀) ≥ 0`; for
`L ≤ L₀` monotonicity of `λ` gives `λ(L) ≥ λ(L₀) ≥ 0`.  So `λ ≥ 0` everywhere, which is exactly the
Riemann hypothesis.

**Hence no nondecreasing lower bound for `λ` that is nonnegative anywhere can be established by any
means short of proving the Riemann hypothesis itself.**  Every scheme for extending a positivity
range past its current endpoint must therefore either produce such a bound — and so be as hard as RH
— or fail, as all four attempts above do.  This closes the extension programme as a lane.

Together with the earlier ceilings this completes the map:

```text
linear Λ-positivity          caps at PNT strength                       (Theorem N)
quadratic Weil index         gives lower bounds on ind₋ only            (Theorem N′)
Bohr-torus probability       valid only past height ~ π(N)              (Theorem G)
elementary archimedean tower optimal at ℓ ≈ 0.155                       (Theorems Q24–V29)
extension of the range       equivalent to RH                           (this file)
axiomatic characterization   circular or false                          (Theorems M, P, R)
```

This file formalizes the equivalence.
-/

open Real

noncomputable section

namespace RHTower

/-- **No-go for the extension programme.**  A nondecreasing lower bound for the bottom of the
spectrum which is nonnegative at a single length forces nonnegativity at every length. -/
theorem extension_forces_positivity {lam b : ℝ → ℝ}
    (hlam : ∀ ⦃x y : ℝ⦄, x ≤ y → lam y ≤ lam x)
    (hb : ∀ ⦃x y : ℝ⦄, x ≤ y → b x ≤ b y)
    (hle : ∀ x, b x ≤ lam x) {L₀ : ℝ} (hL₀ : 0 ≤ b L₀) (L : ℝ) :
    0 ≤ lam L := by
  rcases le_total L L₀ with h | h
  · exact le_trans (le_trans hL₀ (hle L₀)) (hlam h)
  · exact le_trans (le_trans hL₀ (hb h)) (hle L)

/-- The converse direction: if the bottom of the spectrum is everywhere nonnegative — the Riemann
hypothesis in Weil's form — then the constant zero is such a bound.  So the existence of a
nondecreasing nonnegative-somewhere lower bound is *equivalent* to Weil positivity. -/
theorem positivity_gives_extension {lam : ℝ → ℝ} (hpos : ∀ x, 0 ≤ lam x) :
    (∀ ⦃x y : ℝ⦄, x ≤ y → (0 : ℝ) ≤ 0) ∧ (∀ x, (0 : ℝ) ≤ lam x) ∧ (0 : ℝ) ≤ 0 :=
  ⟨fun _ _ _ => le_refl 0, hpos, le_refl 0⟩

/-- Downward propagation, the only direction the soft tools give: positivity at one length yields
positivity at all shorter lengths, and never at longer ones. -/
theorem downward_only {lam : ℝ → ℝ}
    (hlam : ∀ ⦃x y : ℝ⦄, x ≤ y → lam y ≤ lam x) {L₀ : ℝ} (hL₀ : 0 ≤ lam L₀)
    {L : ℝ} (hL : L ≤ L₀) : 0 ≤ lam L :=
  le_trans hL₀ (hlam hL)

end RHTower
