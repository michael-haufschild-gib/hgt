# Positive-part lag criterion

- **ID:** LAG-POS-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** O lane, one-sided lag criterion (STATUS MUST-237, CANNOT-326)
- **Statement:** RH ⟺ for every `η > 0` there is `C` with `∫_0^T max(Φ(u), 0) du ≤ C e^{ηT}` for all `T ≥ 0`, where `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` is the real lag function.

## Theorem
Let `Φ₊ = max(Φ, 0)`, `Φ₋ = max(−Φ, 0)`. Then `Φ₋ = Φ₊ − Φ` is a nonnegative density whose
Laplace transform on `Re s > ½` is `L[Φ₊](s) − G(s)`, `G(s) = Σ_ρ (ρ(1−ρ))⁻¹/(s − (ρ − ½))`.
If `∫_0^∞ Φ₊(u) e^{−σu} du < ∞` for every `σ > a ≥ 0`, then `L[Φ₊]` is analytic on `Re s > a`,
Landau's theorem forces the abscissa of `Φ₋ du + du` down to `a`, and `G = L[Φ₊] − L[Φ₋]` extends
analytically to `Re s > a`; the extension theorem of the lag criterion gives `Re ρ ≤ ½ + a` for
every zero. The integrated hypothesis `∫_0^T Φ₊ ≤ C e^{ηT}` (`η < σ`) gives finite Laplace mass at
`σ` by summing over unit intervals. Under RH, `Φ₊ ≤ 2 + γ − log 4π`, so the primitive is linear.

The same holds with `Φ₋` in place of `Φ₊`. No ceiling on `Φ`, no bound on `|Φ|`, and no
information on the other sign enter.

## Consequences
- The one-sided prime criterion is weakened from a pointwise ceiling on the tail-averaged prime
  deficit to sub-exponential mass of its positive excursions at every rate.
- Under `¬RH` the Laplace abscissa of `Φ₊` equals `Θ − ½` (`Θ = sup Re ρ`): the excursions of `Φ`
  above zero carry exponential mass at the rate of their height. For every `ε > 0`,
  `|{u ≤ T : Φ(u) ≥ e^{(Θ−½−ε)u}}| ≥ e^{−εT}` for infinitely many `T`; the Lipschitz spreading of a
  single peak gives only `e^{(Θ−1)T}`.
- Failed attempt recorded here: bounding `∫_0^T Φ²` by Mellin–Parseval from mean values of
  `ζ'/ζ` on vertical lines `Re s = σ > ½` is circular — Parseval needs the Mellin transform of
  `√x Φ(log x)` to converge on the line, i.e. `Φ = O(e^{(σ−½)u})`, which is the conclusion
  (Cramér's criterion converse is the Paley–Wiener form of the same fact).

## Lean
Module `RHTower/WeilLagFunctionPositivePart.lean` (wired after `WeilLagFunctionGrowth`; axioms
`propext, Classical.choice, Quot.sound`):
`riemannHypothesis_iff_lagPositivePart_integral_subexponential`,
`riemannHypothesis_of_lagPositivePart_laplace`, `riemannHypothesis_of_lagNegativePart_laplace`,
`re_le_half_add_of_lagPositivePart_laplace`, `re_le_half_add_of_lagPositivePart_integral`,
`complexLaplace_oneSidedMeasure_zero_flip`, `laplaceMass_oneSidedMeasure_ne_top_of_integral_le`.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proof complete
- [x] 2 → 3  Lean theorem, module build green, axioms clean
- [ ] 3 → 4  not pursued (no stage 4 by directive)
