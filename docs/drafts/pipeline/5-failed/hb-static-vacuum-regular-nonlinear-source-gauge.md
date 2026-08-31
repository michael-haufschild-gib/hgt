# Failed route: static vacuum-regular nonlinear HB source gauge

- **ID:** HB-STATIC-VACUUM-REGULAR-NONLINEAR-SOURCE-GAUGE
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** A static continuous nonlinear reparametrization preserving literal BM reflected sources might make source-FE transport commute with one fixed physical clock step off the critical wall.

## Exact killing theorem/mechanism
Killed by
`not_exists_hbXiPeierls_vacuumRegular_sourceExchange_clockCovariant_of_offLine`.
Tilt makes the reflected clock orbit hyperbolic: one source axis contracts and its reflected axis
expands. Vacuum regularity plus clock commutation preserves the stable set, while literal source
exchange sends its nonzero stable source into the nonzero unstable source. Iteration contradicts
vacuum convergence.

The formal theorem is stronger than the proposal: the map need not be linear, invertible,
differentiable, norm-preserving, support-local, or orbit-local.

## Strongest positive survivor
Exact classification:

`HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt n t q ↔ Re(q)=1/2`

for every `t ≠ 0`. Universally quantified over Xi copies, the same existence law is equivalent to
RH. Therefore any successful tilted-sector mechanism must violate at least one sharply named
condition: vacuum regularity, literal two-way source exchange, or commutation with the fixed clock.
For physical continuous dynamics, the meaningful survivors are source-changing or genuinely
time-dependent Einstein--Teukolsky evolution.

## New insight
Obstruction is topological/dynamical, not algebraic. Linear rigidity was not doing essential work:
contracting/expanding orientation already prevents every vacuum-regular nonlinear repair. This
removes static nonlinear coordinate engineering from HB and returns remaining burden to literal
time-dependent source dynamics.

## Status
- Paper proof: dependency-closed, `[PROVED HERE]`.
- Lean proof: `ThetaCuspHawkingBMVacuumRegularNonlinearSourceGaugeNoGo.lean`.
- Closed certificate: `d4HBVacuumRegularNonlinearSourceGaugeClockCovarianceRouteKilled`.
- Frontier map was not modified.

## Log
- 2026-08-31 — route killed; exact wall classification formalized.
