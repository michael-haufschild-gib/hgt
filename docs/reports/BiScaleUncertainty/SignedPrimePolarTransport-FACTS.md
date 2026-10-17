# Signed prime–polar transport: facts and failure boundaries

## Counting rule

Target: 100 substantive, independently justified contributions. Verified packages: 0.
Helpers, equivalent restatements, and classical partial summation do not count separately.

## Established inputs

- Pillar XIV retains arbitrary signed node correlations; its Krein increment bound
  controls |h(t+y)−h(t)| by sqrt(2h(0)(h(0)−h(y))).
- Pillar XV proves the reciprocal penalty exp(−y/2)sinh(y) and annular local transport.
- Classical ψ is available as `Chebyshev.psi` in the installed mathlib.
- Compact continuous autocorrelations are continuous via `continuous_autocorr_compact`.

## Exact sign and domain constraints

- Polar density is exp(x/2)+exp(−x/2). Matching prime density to exp(x/2)
  leaves a genuine exp(−x/2) integral; it cannot be discarded.
- With E(x)=ψ(exp x)−exp x, E(0)=−1. Integration by parts contributes +H(0).
- Finite-window endpoints survive unless actual support proves their vanishing.
- Source continuity does not justify differentiating its autocorrelation. An annular
  average H(t)=(b−a)⁻¹∫_a^b h(t+y)dy has the constructed continuous derivative
  (h(t+b)−h(t+a))/(b−a).
- Separate per-node applications spend origin energy repeatedly. A uniform averaging
  estimate followed by the actual total measure mass keeps that cost explicit.

## Open package

The dependency-closed paper proof is in `SignedPrimePolarTransport.md`.
`AnnularCorrelationTransport.lean` passes direct Lean compilation without diagnostics:
the average has an explicit continuous derivative, a uniform Krein-error bound, and
an adjustable annular Lévy penalty. The combined actual arithmetic coupling is still
under audit; these local helper results do not count as a separate package.

## Next cancellation question

The total-mass estimate forgets cancellation in the signed prime–polar measure.
For its actual translated source packet Pν, Cauchy–Schwarz suggests replacing
M_L sqrt(R) by ||Pν||₂ in the averaging cost. The full packet Gram energy includes
prime–prime, prime–polar, and polar–polar terms; none may be omitted. Existing
`translationGramEnergy_eq_integral` supplies the finite discrete case, but does not
by itself construct the continuum polar packet or justify its mixed Fubini terms.
This is a next conjecture, not a verified contribution or a uniform bound.
