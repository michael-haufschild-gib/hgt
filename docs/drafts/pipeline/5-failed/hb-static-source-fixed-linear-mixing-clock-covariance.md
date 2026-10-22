# HB static source-fixed linear mixing clock covariance

- **ID:** hb-static-source-fixed-linear-mixing-clock-covariance
- **Stage:** 5-failed
- **Type:** FALSIFIED ROUTE CLASS
- **Source:** HB source-predeclared finite-clock covariance open core
- **Statement:** Static arbitrary complex-linear mixing cannot manufacture missing nonzero-time HB
  covariance while retaining literal nonlinear source incidence.

## Failed RH chain

```text
static source-fixed packet mixing
  -X-> source-FE covariance at one fixed nonzero physical clock step
  -> total-cokernel extinction
  -> source-FE unit clock gain
  -> HB/FZZ-P/PW-B/RBH Ward cancellation
  -> RH.
```

First arrow exists only if RH already holds. This is a structural route kill, not failure of a
normalization, diagonal ansatz, topology, locality condition, or estimate.

## Exact obstruction

Every tilted FE orbit carries two nonzero literal source packets. A complex-linear equivalence
fixing either source packet fixes that coordinate's entire complex line. Fixing both orbit sources
makes its conjugated source-FE transport identical to literal transport on the orbit. Nonzero-time
covariance then invokes exact literal single-orbit clock rigidity and forces the orbit onto the
critical wall, contradiction.

The classification permits arbitrary global coordinate mixing and assumes no clock, pairing,
support, reflection, norm, topology, basis, or locality preservation. Only invertible complex
linearity and literal source fixing remain.

## Positive survivor

For any tilted orbit and nonzero physical time, a clock-covariant static linear equivalence must
move at least one of the two literal source packets. Thus viable HB research must derive a genuinely
source-changing, nonlinear, or time-dependent producer. Merely mixing physical-clock eigenspaces
without changing source incidence cannot close the route.

No stronger positive salvage survives inside static literal-source-preserving linear conjugacy.

## Paper and Lean status

Dependency-closed proof and hostile scope are recorded in
`../3-formalized/hb-source-fixed-linear-mixing-clock-covariance-no-go.md`.

Lean module:
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFixedLinearMixingClockCovarianceNoGo`.

Main route-kill theorem:
`RHTower.hbXiPeierlsExistsUnitSourceFixedLinearGaugePhysicalClockStepCovariant_iff`.

Positive survivor:
`RHTower.hbXiPeierlsLinearGaugeClockCovariant_sourceDisplacement_of_offLine`.

Closed certificate:
`RHTower.d4HBSourceFixedLinearMixingClockCovarianceRouteKilled`.

Direct Lean check, targeted module build, umbrella wiring, and axiom audit passed on 2026-08-31.

## Log

- 2026-08-31 — full static source-fixed complex-linear mixing class killed; local source-
  displacement law extracted and formalized.

