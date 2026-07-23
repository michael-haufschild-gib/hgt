# Finite superzeta–Fredholm logarithmic-derivative universality law

## Status

Novelty gate failed after exact Lean formalization.

## Lean-generated inputs

- `RHTower/SuperzetaResolvent.lean`: finite superzeta is sum of local resolvents
  `(1 - z rᵢ)⁻¹`.
- `HTGeometry/FredholmDeterminantExamples.lean`: finite diagonal operator, trace-class determinant
  `det₁`, diagonal resolvent trace, and `logDeriv det₁ = -(tr K + resolventTrace K)`.

## Candidate

For every finite spectral packet inside Fredholm disk,
`Σᵢ (1 - z rᵢ)⁻¹ = n - z · logDeriv(det₁(1 - z·diag(r)))`.

## No-go closure

- **Exact killing theorem/mechanism:** Hartmann–Lesch, *Zeta and Fredholm determinants of
  self-adjoint operators* (2021), Eq. 4.3, states the general trace-class identity equating the
  logarithmic derivative of a Fredholm determinant with a resolvent trace. Candidate is its finite
  diagonal specialization plus `tr(I)=n`; it is not literature-new.
- **Strongest positive survivor:** exact corpus connector
  `GaloisForLFunctions.finiteSuperzetaResolventValue_eq_fredholmDet1_logDeriv`.
- **New insight:** corpus's additive superzeta and multiplicative determinant faces are not disjoint;
  `det₁` transforms one into the other after sharp cardinality correction. Hilbert–Carleman
  regularization removes degree zero and trace-class correction restores degree one.
- **Status:** formalized warning-free in
  `RHTower/FiniteSuperzetaFredholmLogDerivativeUniversalityLaw.lean`; external novelty failed.

## Literature

- Luiz Hartmann and Matthias Lesch, *Zeta and Fredholm determinants of self-adjoint operators*,
  arXiv:2106.02444, Eq. 4.3.
