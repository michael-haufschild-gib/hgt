# Archimedean-balanced third-order Perron charge

- **ID:** archimedean-balanced-third-perron
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[PROVED]`
- **Date:** 2026-07-10
- **Module:** `GaloisForLFunctions.RHTower.ArchimedeanBalancedPerron`
- **Paper proof:** `../../2-fully-proven/new/archimedean-balanced-third-perron.md`

## Formal surface

- `balancedPerronKernel_mellin` — exact transform
  `(s-1)/(s(s+1)(s+2))`.
- `balancedPerronKernel_verticalIntegrable` — absolute vertical integrability.
- `balancedPerronKernel_inversion` — inverse Mellin formula.
- `balanced_perron_sum` — Dirichlet-series summation against the balanced physical weight.
- `balancedPerronWeight_third_difference` — exact four-knot charge `3delta^2 a_n/4`.
- `perronThirdKink_zero`, `perronThirdKink_negOne`, `perronThirdKink_negTwo` — cancellation of all
  three denominator points.
- `perronThirdE_differentiable`, `perronThirdE_eq` — entire triple regularization and quotient law.
- `perronThirdBalancedCharge` — exact raw Dirichlet coefficient extraction.
- `boundaryDecompletion_differentiable`, `boundaryDecompletion_eq` — entire reciprocal-Gamma
  regularization.
- `archFactor_mul_boundaryDecompletion` — boundary-balanced identity `archFactor*D_infty=s-1`.
- `boundaryDecompletion_unique` — uniqueness of every exact pointwise scalar decompletion.
- `xi_mul_boundaryDecompletion` — exact loss-of-completion identity
  `xi*D_infty=(s-1)zeta`.
- `completedPerronThirdCharge` — completed Dirichlet coefficient extraction with no defect Prop.
- `xi_completedPerronThirdCharge` — concrete unconditional charge `3delta^2/4` for `xi`.

## Certificate

- Targeted module check: passed.
- Full/umbrella build: deliberately not run.
- Active `sorry`, `admit`, `axiom`, `opaque`, `unsafe`: none.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Generated API refreshed; formal lint passed.

## Scope

This theorem does not provide negative-line mass for the decompleted carrier.  The formal identity
`xi_mul_boundaryDecompletion` proves why: exact scalar extraction returns `(s-1)zeta`.  The next
RH-facing object must evade pointwise scalar decompletion.
