# HB vacuum-regular nonlinear source-gauge no-go

- **ID:** HB-VACUUM-REGULAR-NONLINEAR-SOURCE-GAUGE-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HB surviving source-dynamical clock producer
- **Statement:** At every nonzero physical clock time, a source-axis vacuum-regular packet map can exchange the two literal reflected BM sources and commute with the centered-QNM clock exactly on the critical wall.

## Goal and RH chain
Kill the nonlinear survivor left by the static complex-linear mixing no-go:

`literal BM reflected source exchange`
`→ static nonlinear coordinate repair`
`→ one source-predeclared physical clock covariance`
`→ canonical HB branch covariance`
`→ RH`.

The theorem removes the repair step. It assumes no linearity, differentiability, invertibility,
positivity, norm preservation, support locality, or finite-dimensional orbit preservation.

## Proof
For tilted `q` and nonzero time `t`, exact centered-QNM multipliers on `q` and `Rq` have norms

`exp(t(1/2-Re q)/2)` and `exp(-t(1/2-Re q)/2)`.

Exactly one is strictly contracting and the other strictly expanding. Clock covariance iterates a
literal source on the contracting axis into powers tending to vacuum. Source-axis vacuum
regularity therefore forces every coefficient of its image to tend to zero. Exact reflected
source exchange and clock covariance identify the reflected coefficient with `nu^k B`, where
`|nu|>1` and the off-wall literal reflected source `B` is nonzero. Its norm is at least `|B|`, a
contradiction. The opposite sign of `t(1/2-Re q)` uses the reflected orbit.

On the wall both literal source packets vanish, so the zero map supplies the converse. Thus local
existence is exactly wall placement; universal existence is exactly RH.

## Lean closure
- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVacuumRegularNonlinearSourceGaugeNoGo`
- Main route kill: `not_exists_hbXiPeierls_vacuumRegular_sourceExchange_clockCovariant_of_offLine`
- Exact classification: `hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff`
- Global endpoint: `forall_hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff_rh`
- Closed certificate: `d4HBVacuumRegularNonlinearSourceGaugeClockCovarianceRouteKilled`
- Umbrella: `GaloisForLFunctions.RHTower`

## Novelty/hostile audit
Internal corpus contained arbitrary clock-preserving gauges, diagonal gauges, static complex-linear
source-fixed mixing, transported positive Hermitian metrics, and a distinct regular-Fock
occupation-recurrence obstruction, but no vacuum-regular nonlinear packet-map classification.
The Fock result constrains nonzero square-summable transformed vacua; this theorem instead permits
an arbitrary nonlinear map on all finite Xi packets and uses only one-axis vacuum regularity.
Generic hyperbolic-dynamics literature contains stable/unstable-set invariance;
the source-faithful BM/Xi classification and its HB route consequence were not found in the
August 2026 audit. Novelty is the exact source/clock application and removal of all algebraic gauge
hypotheses, not the elementary stable-set lemma in isolation.

## Gates
- [x] Complete dependency-closed paper proof
- [x] Unconditional Lean theorem; no new axioms or hypotheses hidden in the route certificate
- [x] Wired into umbrella
- [x] Targeted module build and `#print axioms` audit pass (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] Repository-wide lint is currently blocked by two unrelated untracked modules not wired by their owners; this module is reachable and direct/targeted checks pass
- [ ] Publication-ready standalone note

## Log
- 2026-08-31 — `[PROVED HERE]`; paper proof and Lean formalization closed.
