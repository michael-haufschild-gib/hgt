# Route E reciprocal-allocation Jacobian and capacity finite core

- **ID:** `ROUTE-E-RECIPROCAL-ALLOCATION-JACOBIAN-CAPACITY-FINITE-CORE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT FINITE KERNEL LAW
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-reciprocal-allocation-square-root-jacobian-carleson-reduction.md`
- **RH used:** no
- **Computation used:** no

## Exact theorem package

For any finite allocation system with positive allocation scales, nonempty admissible families,
and nonempty physical terminal fibres, reciprocal mass `1/T` followed by uniform mass inside each
fibre defines a nonnegative kernel. Coincident allocation representations are added after physical
projection. Lean proves row sum exactly one.

When forward terminal count carries `T^(-1/2)` and inverse physical multiplicity carries
`T^(1/2)`, reciprocal allocation cancels both square-root Jacobians exactly. General power tilt
leaves column exponent `1-lambda`, so `lambda=1` is unique scale-neutral tilt.

For every finite nonnegative row-stochastic kernel, total mass is source cardinality and some
physical column has load at least

```text
card(source) / card(target).
```

This is representation-independent finite capacity conservation.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.MobiusReciprocalAllocationJacobian
```

Principal declarations:

```text
ReciprocalAllocationSystem.sum_harmonicKernel
reciprocalAllocation_squareRootJacobian_cancel
reciprocalAllocation_scaleNeutral_iff
FiniteRowStochasticKernel.total_mass
FiniteRowStochasticKernel.exists_average_le_column
```

Module is umbrella-reachable through whole-anchor/parity modules. Direct source check passes;
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

No asymptotic structured-token count or `1+o(1)` physical-column law is proved here. The finite
theorem removes reservoir-scale algebra; fine arithmetic incidence and normalized seam flux remain
open.

## Log

- 2026-08-12 — corpus-growth audit verified and promoted exact reciprocal finite core.
