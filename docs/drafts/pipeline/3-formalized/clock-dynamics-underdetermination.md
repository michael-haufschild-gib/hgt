# Clock-reconstructed geometry does not select Einstein dynamics

- **ID:** `clock-dynamics-underdetermination`
- **Stage:** 3-formalized
- **Type:** EXACT NO-GO / POSITIVE AXIOM BOUNDARY / GRAVITATIONAL DYNAMICS
- **Parent:** `../1-in-progress/quantum-clock-compass-chronodromy-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ClockDynamicsUnderdetermination.lean`
- **Status:** unconditional Lean algebra; geometric Bianchi input remains a physical theorem

## Killed claim

> Complete clock geometry plus Bianchi consistency and stress-energy conservation uniquely forces
> Einstein dynamics.

This is false when matter source is not fixed independently.

Let a complete clock network reconstruct `g` and its Einstein tensor `G`. For nonzero coupling
`kappa`, define

```text
T_eff = kappa^(-1) (G + Lambda g).
```

The contracted Bianchi identity and metric compatibility give

```text
div G = 0,
div g = 0,
div T_eff = 0,
G + Lambda g = kappa T_eff.
```

Thus every reconstructed geometry admits a conserved effective source satisfying an
Einstein-form equation. Geometry plus conservation cannot distinguish fundamental matter from
geometric corrections moved to the source side.

## Positive survivor

Clock algebra can reconstruct gravitational kinematics. Dynamics requires an independent
source-response principle. The minimal live strengthening is:

> Two theories are chronometrically equivalent only if they agree on the complete interventional
> map from independently calibrated matter-source changes to changes of the clock observable net.

In four dimensions, adding locality, a metric-only natural symmetric tensor, second derivative
order, and divergence freedom reaches the Lovelock/HKT uniqueness boundary. Novel work must derive
or operationally replace those assumptions; quoting them after assuming metric phase space is not
a new origin of gravity.

## Formal surface

The module exports:

- `effectiveStressTensor`;
- `effectiveStressTensor_conserved`;
- `einsteinEquation_effectiveStressTensor`;
- `exists_conserved_effectiveStressTensor`.

No tensor is called Einstein or metric by axiom. The Lean theorem takes a linear divergence map and
explicitly stated divergence-free hypotheses; physical differential geometry supplies their
interpretation.

## Verification

- Direct foreground check:
  `lake env lean GaloisForLFunctions/HTGeometry/ClockDynamicsUnderdetermination.lean`
  passed on 2026-07-28.
- `#print axioms` and final module build remain deferred to the final batch audit.

