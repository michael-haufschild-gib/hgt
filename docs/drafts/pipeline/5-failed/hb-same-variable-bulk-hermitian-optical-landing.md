# HB same-variable bulk Hermitian optical landing

- **ID:** hb-same-variable-bulk-hermitian-optical-landing
- **Stage:** 5-failed
- **Type:** FALSIFIED ROUTE CLASS
- **Source:** HB open core in `ThetaCuspHawkingSchwarzianOpticalTheoremEndpoint`
- **Statement:** A fixed-phase pointwise Hermitian anomaly in one holomorphic complex-frequency
  variable cannot equal the actual balanced theta-Hawking Born channel on any nonempty open set.

## Failed RH chain

```text
same-variable bulk Hermitian optical identity
  -X-> opposite-sign complete HB causal orbit
  -> total-cokernel extinction
  -> source-FE unit clock gain
  -> HB/FZZ-P/PW-B/RBH Ward cancellation
  -> RH.
```

The first arrow is unavailable within this entire route class. This is a structural kill, not a
failed normalization or bound.

## Exact obstruction

Every pointwise term `conj(B)C + conj(C)B` is real. If a fixed nonzero phase times such a term
equals the actual Hawking Born amplitude on an open complex domain, phase-rescaled amplitude is a
real-valued holomorphic function on an interior ball. It must be locally constant; analytic
continuation makes it globally constant. Exact anchors contradict this: amplitude is zero at `0`
and nonzero at `1`.

The theorem allows arbitrary `B,C`, arbitrary fixed nonzero phase, disconnected domain, and only
local-open equality. Making coefficient channels less regular does not evade the obstruction.

## Positive survivor

Keep conjugated data in an independent Schwarz variable:

```text
Hsharp(B,C;z,w)
  = conj(B(conj(w))) C(z) + conj(C(conj(w))) B(z).
```

If `B,C` are entire, `Hsharp` is holomorphic separately in `z` and `w`; restriction to
`w=conj(z)` recovers the original Hermitian anomaly exactly. Therefore surviving HB research must
do one of the following:

1. derive a genuinely two-variable polarized optical identity before taking the physical diagonal;
2. use real-axis boundary values or distributions rather than an open bulk identity;
3. use a nonlocal kernel/operator identity that is not pointwise Hermitian in one variable.

No other positive salvage remains inside same-variable bulk-local holomorphy.

## Paper and Lean status

Dependency-closed paper proof and positive survivor are recorded in
`../3-formalized/hb-bulk-holomorphic-hermitian-optical-no-go.md`.

Lean module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBulkHolomorphicHermitianOpticalNoGo`.

Main route-kill theorem:
`RHTower.not_thetaCuspHawkingSameVariableLocalHermitianOpticalLanding`.

Closed certificate:
`RHTower.thetaCuspHawkingBulkHermitianOpticalNoGoCertificate`.

Direct Lean check, targeted module build, umbrella wiring, and axiom audit passed on 2026-08-31.

## Log

- 2026-08-31 — route killed locally on every nonempty open complex-frequency domain; strongest
  two-variable Schwarz-polarized survivor extracted and formalized.
