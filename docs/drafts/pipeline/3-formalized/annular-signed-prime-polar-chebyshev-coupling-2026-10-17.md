# Annular signed prime–polar Chebyshev coupling

- **ID:** annular-signed-prime-polar-chebyshev-coupling
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `1-in-progress/signed-prime-polar-transport-2026-10-17.md`
- **Contribution count:** one package; helpers and classical summation are not separate contributions.
- **Paper:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport.md`

## Exact result

Every compact continuous real source has a constructed C¹ annular correlation
average. At each L=log(N+2), its original signed von Mangoldt–polar pairing differs
from the average's exact Chebyshev work by at most total prime-plus-polar mass
times the origin Krein averaging cost. That cost admits an adjustable local Lévy
bound with the reciprocal weight exp(−y/2)sinh y. The work includes both endpoints
and the negative-exponential polar term. No grid zeros, source derivative, unknown
arithmetic estimate, full-energy finiteness, or nonzero-source premise is assumed.

## Lean evidence

Modules, both in `formal/GaloisForLFunctions/BiScaleUncertainty/`:

- `AnnularCorrelationTransport.lean`: derivative construction, uniform local error,
  and adjustable reciprocal-weight penalty.
- `SignedPrimePolarCoupling.lean`: actual atom cumulative measure, exact Chebyshev
  identity, literal pairing equality, and original-source error bound.

Main endpoint: `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar.abs_pairing_sub_chebyshevWork_le_levy`.
Both direct `lake --old env lean` leaf audits exit 0 without diagnostics; both
imports are wired. Six endpoint axiom checks report only propext, Classical.choice,
Quot.sound. The printed main signatures contain only actual source and parameters.
Indexes regenerated. Global lint reports one unrelated concurrent wiring error
for `RHTower.FermiNymanDyadicFoldGeometry`; no task-local lint error is reported.

## Boundaries

The formal identity covers every finite integer truncation; full half-line support
closure remains open in this lane. The total-mass factor remains explicit, so no
cutoff-uniform estimate follows. The average need not itself be positive definite.
No external novelty or publication-ready claim is made.

## Gates

- [x] Well-posed source domain and signed measure target.
- [x] Dependency-closed paper proof.
- [x] Direct leaf Lean verification, axiom audit, and umbrella wiring.
- [ ] Publication-ready external novelty and exposition audit.
