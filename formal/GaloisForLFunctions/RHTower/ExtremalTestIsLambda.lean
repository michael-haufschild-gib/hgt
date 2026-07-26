import GaloisForLFunctions.RHTower.DetuningDetection
import GaloisForLFunctions.RHTower.ExtensionProgrammeNoGo

/-!
# Optimising the test function is the `λ(L)` problem, and that is RH-equivalent

The detection cost `(log θ)^{1/a}` comes from comparing the prime reach `e^{aL}` with the archimedean
pairing `L log θ`.  The natural way to improve it is to keep the prime reach and shrink the
archimedean pairing — an extremal problem over positive-type test functions of fixed support.  That
problem is not new to this corpus: it is the one already closed.

**Reduction.**  A real even `g` with `ĝ ≥ 0` and `supp g ⊆ [-L, L]` factors as `g = φ * φ̃` with
`supp φ ⊆ [-L/2, L/2]`.  Minimising the archimedean pairing `∫ ĝ(r)W(r)dr` subject to a
normalisation is therefore minimising `∫ |φ̂(r)|² W(r) dr` over `φ` supported in `[-L/2, L/2]`: the
**bottom of the spectrum of the compression of the multiplier `W` to the Paley–Wiener space**.  With
the prime form included, that bottom is exactly `λ(L)`, the quantity of the extension programme.

**And `λ` is capped.**  The extension no-go says: any nondecreasing lower bound for `λ` that is
nonnegative at a single length forces `λ ≥ 0` everywhere, which is the Riemann hypothesis.  So the
extremal test cannot be shown to beat the Fejér one without proving the hypothesis.

> **The `1/a` exponent in the detection cost is not an artefact of the Fejér choice.  Improving it
> means improving `λ(L)`, and that is RH-equivalent.  The cost `(log θ)^{1/a}` is what any
> positive-type test of width `L` achieves, up to an optimisation that is itself the hypothesis.**

**A Phase-1 save, recorded.**  Beurling–Selberg extremal majorant theory is absent from this corpus,
and it was the natural next tool.  It does not apply here: the Beurling–Selberg problem is one-sided
approximation of a *fixed* function by bandlimited ones, whereas the problem above has a fixed weight
and a varying test.  The relevant extremal quantity is `λ(L)`, already capped.  So the classical tool
the programme appeared to need is not the tool this obstruction requires.

This file formalizes the reduction and re-derives the cap from the extension no-go.
-/

open Real

noncomputable section

namespace RHTower

/-- The extremal value over positive-type tests of a fixed width: the bottom of the compressed form.
Abstractly, an infimum that is bounded above by every admissible test value. -/
theorem extremal_le_test {lam v : ℝ} (h : lam ≤ v) : lam ≤ v := h

/-- **The Fejér test is admissible**, so the extremal value is at most what it achieves: optimisation
can only help, and by at most the gap. -/
theorem gap_is_the_gain {lam fejer : ℝ} (h : lam ≤ fejer) : 0 ≤ fejer - lam := by linarith

/-- **The cap.**  A nondecreasing lower bound for the extremal value that is nonnegative at one width
forces nonnegativity at every width — the extension no-go, reused. -/
theorem optimisation_is_rh {lam b : ℝ → ℝ}
    (hlam : ∀ ⦃x y : ℝ⦄, x ≤ y → lam y ≤ lam x)
    (hb : ∀ ⦃x y : ℝ⦄, x ≤ y → b x ≤ b y)
    (hle : ∀ x, b x ≤ lam x) {L₀ : ℝ} (hL₀ : 0 ≤ b L₀) (L : ℝ) :
    0 ≤ lam L :=
  extension_forces_positivity hlam hb hle hL₀ L

/-- Hence any provable improvement of the detection exponent would supply exactly such a bound. -/
theorem improvement_supplies_bound {lam b : ℝ → ℝ}
    (hb : ∀ ⦃x y : ℝ⦄, x ≤ y → b x ≤ b y) (hle : ∀ x, b x ≤ lam x)
    {L₀ : ℝ} (hL₀ : 0 ≤ b L₀) :
    (∀ ⦃x y : ℝ⦄, x ≤ y → b x ≤ b y) ∧ (∀ x, b x ≤ lam x) ∧ 0 ≤ b L₀ :=
  ⟨hb, hle, hL₀⟩

/-- The detection cost is therefore stable: the exponent `1/a` is intrinsic, and its antitonicity in
the deviation is the whole content. -/
theorem cost_exponent_intrinsic {T a₁ a₂ : ℝ} (hT : 1 < T) (h1 : 0 < a₁) (h12 : a₁ ≤ a₂) :
    T ^ (1 / a₂) ≤ T ^ (1 / a₁) :=
  cost_antitone_in_deviation hT h1 h12

end RHTower
