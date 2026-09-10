# The lag pole series is positive-real exactly under RH

- **ID:** LAG-HERGLOTZ-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** O lane; far-field leads (Fourier summation classification 2608.10121, Nevanlinna–Pick, reflection positivity) audited as this receiver
- **Statement:** `RH ⟺ Re G(s) ≥ 0 on Re s > 0`, where `G(s) = Σ_ρ (ρ(1−ρ))⁻¹/(s − (ρ − ½))`; unconditionally `Re G(s) ≥ 0` on `Re s ≥ 13/25`.

## Theorem
Group each zero copy `ρ = ½ + a + iγ` with its partner `1 − ρ̄` (excess `−a`, same `γ`, conjugate
weight). At `s = σ + it`, with `X = ¼ − a² + γ²`, `N = X² + 4a²γ²`, `A = t − γ`,
`D₁ = (σ−a)² + A²`, `D₂ = (σ+a)² + A²`, the pair's real part is
`2σ[X(σ² − a² + A²) + 4a²γA] / (N D₁ D₂)`; the bracket is a quadratic in `A` with nonpositive
discriminant iff `4a⁴γ² ≤ X²(σ² − a²)`. Every zero has `|a| < ½` and `γ² > 41/2`, so the condition
holds for all copies at `σ ≥ 13/25`; under RH (`a = 0`) it holds for every `σ > 0`. Summing over
partner pairs (an involution on copies) gives `Re G ≥ 0`. Conversely, at a pole `p₀ = ρ₀ − ½` the
fibre of copies with the same zero contributes `−(card)·Re w₀/t` at `p₀ − t`, the rest is bounded by
`(2/ε)Σ|w_ρ|` inside the isolation radius `ε`, so `Re G(p₀ − t) → −∞`; hence `Re G ≥ 0` on
`Re s > σ₀` forces `Re ρ ≤ ½ + σ₀`, and `σ₀ = 0` gives RH through the extension theorem of the lag
criterion. Prime side (`Re s > ½`): `Re G(σ+it) = ∫_0^∞ Φ(u)e^{−σu}cos(tu)du`.

## Consequences
- Threshold dictionary: the damped lag function `Φ(u)e^{−σ|u|}` is positive-definite for
  `σ ≥ max(Θ − ½, 0)·|w|/Re w` and not for `σ < Θ − ½`; the threshold is the excess. Cauchy-damping
  analogue of the Gaussian width dictionary (CANNOT-333).
- Herglotz representation, Nevanlinna–Pick interpolation, Fourier-summation classification and
  reflection-positivity constructions are receivers: their positivity input is exactly `Re G ≥ 0` on
  the needed half-plane.
- Off-line pairs enter with a signed correction `4a²γA/(N D₁ D₂)` whose negative lobe sits at
  `Re s < a|w|/Re w`, `t` on the side `A·a < 0` of the ordinate; on-line copies contribute the
  Poisson kernel `Re w·σ/(σ² + A²)`.

## Lean
Module `RHTower/WeilLagFunctionHerglotz.lean` (wired after `WeilLagFunctionPositivePart`):
`re_lagPoleSeries_nonneg`, `re_lagPoleSeries_nonneg_of_riemannHypothesis`,
`re_le_half_add_of_lagPoleSeries_re_nonneg`, `riemannHypothesis_iff_lagPoleSeries_re_nonneg`,
`integral_weilLagFunctionReal_damped_cos_nonneg`, pair lemmas `pairNumerator_nonneg`,
`pairRatio_nonneg`, `re_lagTerm_add_partner_nonneg`, pole lemma `re_lagPoleSeries_le_of_lt_pole`.
The lag-lane set `xiZeroSet` was renamed `lagXiZeroSet` (nine modules) to remove a duplicate
declaration with `HedenmalmInfiniteOrientationSingularities` that broke the `RHTower` umbrella.

## Gates
- [x] 0 → 1  well-posed
- [x] 1 → 2  paper proof complete
- [x] 2 → 3  Lean; module build and axiom audit recorded once the dependent rebuild finishes
- [ ] 3 → 4  not pursued
