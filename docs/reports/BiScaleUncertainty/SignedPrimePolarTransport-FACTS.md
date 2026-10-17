# Signed prime–polar transport: facts and failure boundaries

## Counting rule

Target: 100 substantive, independently justified contributions. Verified packages: 1.
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

## Contribution 1: continuous-source signed Chebyshev coupling

The dependency-closed paper proof is in `SignedPrimePolarTransport.md`.
`AnnularCorrelationTransport.lean` and `SignedPrimePolarCoupling.lean` establish one
combined package. For every actual compact continuous source and every integer
cutoff L=log(N+2), its original signed prime–polar pairing differs from explicit
Chebyshev work of a constructed C¹ collar average by at most M_L K. The exact work
retains H(0), the upper endpoint, and the negative-exponential polar shadow. K is
bounded by η times annular Lévy energy plus R/(2ηd²) times the reciprocal-weight
integral. No blindness, source derivative, arithmetic bound, finite full Lévy
energy, or nonzero-source premise occurs in either main theorem.

Public endpoints in namespace `SignedPrimePolar`:
- `pairing_eq_literal`: exact requested n=2,...,N+2 atom sum and polar integral.
- `pairing_correlationAverage_eq`: exact Chebyshev work identity.
- `abs_pairing_sub_chebyshevWork_le`: original-source coupling with uniform Krein cost.
- `abs_pairing_sub_chebyshevWork_le_levy`: adjustable local Lévy/reciprocal-weight bound.

Both leaves pass `lake --old env lean <leaf> -o <leaf.olean>` without diagnostics.
Six endpoint axiom audits in `/tmp/spp_final_axioms.lean` pass, with only propext,
Classical.choice and Quot.sound; printed main signatures contain no extra premise.
Both leaves are wired into `BiScaleUncertainty.lean`; indexes were regenerated.
Repository lint was run and reports one unrelated concurrent wiring error:
`RHTower.FermiNymanDyadicFoldGeometry` is unreachable from `RHTower.lean`.
Logs: `/tmp/spp-final-axioms.log`, `/tmp/spp-index.log`, `/tmp/spp-lint.log`.

Boundary: the formal result is at every finite integer cutoff, not yet a full
half-line identity. M_L is explicit and grows with the window; no cutoff-uniform
bound follows. Averaging, partial summation, and local Young inequalities are
components of this single contribution, not separately counted contributions.

Reusable Lean detail: the chain-rule derivative of exp(−x/2) can expose `(-id) x`.
Reduce `Pi.neg_apply` and `id_eq` before ring normalization. For restricted-measure
indicator integrability use `Integrable.indicator` explicitly; field notation on
an `IntegrableOn` proof selects a different interface.

## Next cancellation question

The total-mass estimate forgets cancellation in the signed prime–polar measure.
For its actual translated source packet Pν, Cauchy–Schwarz suggests replacing
M_L sqrt(R) by ||Pν||₂ in the averaging cost. The full packet Gram energy includes
prime–prime, prime–polar, and polar–polar terms; none may be omitted. Existing
`translationGramEnergy_eq_integral` supplies the finite discrete case, but does not
by itself construct the continuum polar packet or justify its mixed Fubini terms.
This is a next conjecture, not a verified contribution or a uniform bound.
