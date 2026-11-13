# The critical half-line Laplace multiplier is outer

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** B104; Hardy cyclicity of the actual critical state.
- **Statement:** RH holds, or an actual critical half-line ground state has an outer Cayley-composed Laplace multiplier.

## Mathematical advance

Closed-half-plane zero-freeness alone permits a nonconstant singular inner factor at infinity. The actual weak equation also forces positive square mass in every terminal interval. Together these facts eliminate that factor: the actual Laplace multiplier is cyclic for the disk Hardy shift.

## Proof

The critical profile belongs to L¹∩L². Its reflected Laplace transform is bounded and Hardy, and extends continuously without zeros to the closed right half-plane. After Cayley composition, write its canonical factorization as `IO`. The harmonic defect `-log|I|` has representing measure supported at the single boundary point `1`: compact arcs avoiding `1` have bounded radial defect tending almost everywhere to zero, so their Poisson mass vanishes.

Consequently `I(z)=c exp(-d(1+z)/(1-z))`, with `|c|=1` and `d≥0`. The bounded quotient obtained by removing this delay remains Hardy: Cauchy regularization, the Paley–Wiener boundary limit, and dominated convergence retain the original mass bound. Laplace–Plancherel then forces zero square mass on every `(0,a)` with `a<d`. Positive endpoint mass excludes `d>0`. The inner factor is constant, proving outerness.

## Lean audit

Application: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean`.

- `criticalHalfLineGroundState_laplaceMultiplier_outer`
- `riemannHypothesis_or_exists_outerLaplace_criticalHalfLineGroundState`

Reusable argument: `HTGeometry/HardyBoundary/NegativeHalfLineLaplaceOuter.lean`, with pure-delay classification, Hardy delay division, and support-gap lemmas in the same folder. Actual inputs: [boundary zero exclusion](critical-half-line-boundary-laplace-exclusion.md) and [endpoint support](critical-half-line-terminal-support.md).

Plain `lake --old env lean` source audits passed. The unconditional theorem's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Modules are wired into their programme umbrellas.

The [Cayley transport argument](critical-half-line-ground-state-outerness.md) also proves physical causal-translation density. These results do not settle polar pairing or supply the positive finite-window margins required by B4's outer-predictor criterion.
