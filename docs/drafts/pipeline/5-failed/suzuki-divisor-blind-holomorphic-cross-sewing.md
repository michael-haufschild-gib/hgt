# Suzuki divisor-blind holomorphic cross-sewing

- **ID:** suzuki-divisor-blind-holomorphic-cross-sewing
- **Stage:** 5-failed
- **Type:** FALSIFIED ROUTE CLASS
- **Source:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Statement:** Analytic distinct-channel cross-sewing cannot regularize an Xi zero without
  already carrying its divisor through source values or first jets.

## Failed RH chain

```text
Xi-independent divisor-blind holomorphic source channels
  -X-> holomorphic opposite-shift cross-sewn exterior at every nonreal point
  -> Suzuki FE-reflected wall Ward assembly
  -> shared HB/FZZ-P/PW-B/RBH Ward cancellation
  -> RH.
```

The first arrow fails locally at every Xi zero. This is independent of shift, Xi-zero multiplicity,
both interval corrections, and the global origin of the analytic source channels.

## Exact obstruction

The shifted Suzuki target has an actual simple zero at every Xi zero and exact first jet
`z² / ord_z(XiC)`. Its totalized inverse is assigned value zero at the same point. A source simple
zero cancels the reciprocal pole only on the punctured germ: the quotient tends to a nonzero value
but retains totalized center value zero, so it is discontinuous and cannot be analytic.

For the sewn characteristic `P=2 WPlus WMinus`, analyticity therefore requires
`P(z)=P'(z)=0`. Product-jet algebra classifies this as exactly one of:

```text
WPlus(z)=WMinus(z)=0,
WPlus(z)=WPlus'(z)=0,
WMinus(z)=WMinus'(z)=0.
```

## Positive survivor

Holomorphic distinct-channel sewing survives only if source construction derives one of those
three incidences. It must split the Xi zero across both channels or produce a double zero in one
channel. Otherwise it must leave the analytic local class through singular or nonlocal source
data.

This is strongest positive salvage: the no-go does not reject all cross-sewing; it identifies the
exact two-jet divisor information every viable cross-sewn producer must supply.

## Paper and Lean status

Dependency-closed proof, hostile corpus/literature audit, and full certificate are recorded in
`../3-formalized/suzuki-cross-sewn-double-jet-divisor-no-go.md`.

Lean module:
`GaloisForLFunctions.RHTower.Suzuki.SuzukiCrossSewnDoubleJetDivisorNoGo`.

Exact classifier:
`RHTower.analyticAt_suzukiCrossSewnExterior_iff_channelIncidence`.

Closed route kill:
`RHTower.not_suzukiCrossSewnDivisorBlindHolomorphicRegularization`.

Direct Lean check, targeted module build, umbrella wiring, axiom audit, and formal lint passed on
2026-08-31.

## Log

- 2026-08-31 — full divisor-blind holomorphic distinct-channel sewing class killed; exact
  double-jet source-incidence survivor formalized.
