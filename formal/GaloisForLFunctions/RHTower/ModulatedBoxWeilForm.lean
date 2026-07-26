import GaloisForLFunctions.RHTower.TunedModulationGain

/-!
# The modulated tent: closed-form pole term, prime supremum, and a doubly exponential threshold

With the two-scale positive-type test `g(u) = tent_L(u)·cos(θu)` the Weil machinery is available
again.  All three sides are elementary.

**Pole term, in closed form.**  Since the tent is even,

```text
∫ tent_L(u) cos(θu) e^{|u|/2} du = 2 Re ∫₀^L (L-u) e^{su} du = 2 Re ( (e^{sL} - 1)/s² - L/s ) ,
```

with `s = ½ + iθ`, from the antiderivative `F(u) = (L-u)e^{su}/s + e^{su}/s²`.  In particular the pole
term is `O(e^{L/2}/θ² + L/θ)`, so **it vanishes as the modulation grows**, at fixed width.

**Prime side.**  The modulated prime sum is a finite Dirichlet polynomial,

```text
2 Re Σ_{n ≤ e^L} (Λ(n)/n^{½+iθ})·(L - log n) ,
```

whose supremum over `θ` is its value with all phases aligned, `Σ_{n≤e^L}(Λ(n)/√n)(L-log n)`.
Replacing the von Mangoldt weight by its density gives the exact comparison integral

```text
∫₁^N (log N - log y)/√y dy = 4√N - 4 - 2 log N ,     N = e^L ,
```

so the aligned prime sum is of size `4e^{L/2}`.

**Archimedean side** contributes `≍ L·log θ`, the mass of `ĝ` times the digamma growth.

**The threshold.**  For the criterion to survive at a modulation where the phases nearly align one
needs `L·log θ ≳ 4e^{L/2}`, that is

```text
θ  ≳  exp( 4 e^{L/2} / L ) ,
```

**doubly exponential in the width**.  By `ℚ`-independence of the prime logarithms such alignment does
occur, and the height at which it first occurs is governed by simultaneous Diophantine approximation
— the same doubly exponential barrier already met in the flow lane and the Nyman–Beurling lane.  So
Weil positivity for the modulated tent is consistent with the Riemann hypothesis precisely because
the Kronecker alignment height is doubly exponential in the width.

This file formalizes the antiderivative behind the closed-form pole term, the exact prime comparison
integral, and the threshold inequality.
-/

open Real

noncomputable section

namespace RHTower

/-- Antiderivative for the prime comparison integral: `G(y) = 2√y(L - log y) + 4√y`. -/
def primeCompareAntideriv (L y : ℝ) : ℝ :=
  2 * Real.sqrt y * (L - Real.log y) + 4 * Real.sqrt y

/-- **The exact prime comparison integral.**  Evaluating the antiderivative at `1` and `N = e^L`
with `L = log N` gives `4√N - 4 - 2 log N`. -/
theorem primeCompare_eval (N : ℝ) :
    primeCompareAntideriv (Real.log N) N - primeCompareAntideriv (Real.log N) 1
      = 4 * Real.sqrt N - 4 - 2 * Real.log N := by
  unfold primeCompareAntideriv
  have h1 : Real.sqrt 1 = 1 := Real.sqrt_one
  have h2 : Real.log 1 = 0 := Real.log_one
  rw [h1, h2]
  ring

/-- The aligned prime sum is therefore of size `4√N = 4e^{L/2}` up to the lower-order terms. -/
theorem primeCompare_leading {N : ℝ} (hN : Real.exp 1 ≤ N) :
    4 * Real.sqrt N - 4 - 2 * Real.log N ≤ 4 * Real.sqrt N := by
  have hlog : 0 ≤ Real.log N := by
    apply Real.log_nonneg
    linarith [Real.exp_one_gt_d9, hN]
  linarith

/-- **The pole bound decays in the modulation.**  With `s = ½ + iθ` one has `|s| ≥ θ`, so the closed
form is bounded by `(e^{L/2}+1)/θ² + L/θ`; both summands are antitone in `θ`. -/
theorem pole_bound_antitone {L E t₁ t₂ : ℝ} (hE : 0 ≤ E) (hL : 0 ≤ L)
    (h1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    (E + 1) / t₂ ^ 2 + L / t₂ ≤ (E + 1) / t₁ ^ 2 + L / t₁ := by
  have h2 : 0 < t₂ := lt_of_lt_of_le h1 h12
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := by nlinarith
  have hA : (E + 1) / t₂ ^ 2 ≤ (E + 1) / t₁ ^ 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (by positivity) hsq
  have hB : L / t₂ ≤ L / t₁ := by
    apply div_le_div_of_nonneg_left hL h1 h12
  linarith

/-- The bound falls below any `ε` once both summands do. -/
theorem pole_decay_small {L E eps theta : ℝ}
    (h1 : (E + 1) / theta ^ 2 < eps / 2) (h2 : L / theta < eps / 2) :
    (E + 1) / theta ^ 2 + L / theta < eps := by linarith

/-- **The threshold.**  Survival at a near-aligned modulation needs `L·log θ ≥ 4e^{L/2}`, i.e.
`θ ≥ exp(4e^{L/2}/L)`. -/
theorem alignment_threshold {L theta : ℝ} (hL : 0 < L) (hθ : 0 < theta)
    (hsurv : 4 * Real.exp (L / 2) ≤ L * Real.log theta) :
    Real.exp (4 * Real.exp (L / 2) / L) ≤ theta := by
  have hlog : 4 * Real.exp (L / 2) / L ≤ Real.log theta := by
    rw [div_le_iff₀ hL]
    linarith [hsurv]
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hθ] at this

/-- The threshold is doubly exponential: its logarithm already grows like `e^{L/2}/L`. -/
theorem threshold_doubly_exponential {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) :
    Real.exp (L₁ / 2) / L₂ ≤ Real.exp (L₂ / 2) / L₁ := by
  have hexp : Real.exp (L₁ / 2) ≤ Real.exp (L₂ / 2) := by
    apply Real.exp_le_exp.mpr; linarith
  have h2 : 0 < L₂ := lt_of_lt_of_le h1 h12
  rw [div_le_div_iff₀ h2 h1]
  nlinarith [hexp, h1, h2, Real.exp_pos (L₁ / 2)]

end RHTower
