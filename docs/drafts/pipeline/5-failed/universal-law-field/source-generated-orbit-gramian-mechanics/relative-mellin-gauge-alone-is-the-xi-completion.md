# Relative Mellin gauge alone is the Xi completion

- **ID:** ULF-EHGM-FAIL-001
- **Stage:** 5-failed
- **Type:** FALSIFIED completion identification
- **Parent:** ULF-EHGM-001

## Claim tested

The unique dilation-equivariant Mellin multiplier between the order-six aperture/Gamma source
and cubic Euler/Hellinger source is itself the missing completed-Xi landing.

## Exact killing theorem

`M h_lambda=f_lambda` preserves the slowest radial exponential `exp(-lambda t)`.  Every primitive
Euler rate satisfies `lambda>=log 2`; every strict-right Xi conormal rate satisfies
`0<a<1/2<log 2`.  The corpus's primitive spectral-floor/Douglas-range and aperture-intertwiner
no-gos therefore apply: no rate-preserving equivariant map can produce the Xi column.

## Strongest positive survivor

Completion has two distinct typed components:

```text
source coherent-gauge change M  [constructed uniquely]
noncommuting polar--Gamma rate change R  [open].
```

`M` fixes the universal zero-trace metric anomaly that `R` must retain.  The actual open theorem is
an augmented conservation law for `R` whose commutator carries the source/target spectral gap.

## New insight

Gauge change and completion were being conflated.  Gauge change alters cross-label incidence while
preserving local rates; analytic completion must create slower modes and hence break aperture
intertwining.  No further dilation-equivariant source multiplier can close RH.

## Status

Dependency-closed paper no-go from ULF-EHGM-001 plus the audited Lean spectral-floor and
aperture-intertwiner theorems.  Current pass is Lean-read-only.
