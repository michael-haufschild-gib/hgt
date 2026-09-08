# Logarithmic-scale energy as a positive-rate gap detector

- **ID:** SELBERG-LOG-SCALE-GAP-DETECTOR
- **Stage:** 5-failed, for the modal gap inference only.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 9.

## Failed inference

The logarithmic-scale energy of a dyadic Poisson response distinguishes small positive rates and hence could alone exclude exceptional spectral rates.

## Exact obstruction

The actual integral of the squared response in `dt/t` equals `log(9/8)` for every positive rate. Lean proves this evaluation and constancy. No rate threshold can be inferred from this number alone. This does not retire the boundary square-function identity or its possible use together with arithmetic information.

## Positive survivor

The actual integral in `dt` equals `1/(12*r)`, determines the rate injectively, and ranges over exactly the positive reals. Both integrability statements and both integral evaluations are proved in Lean. The [positive-survivor card](../3-formalized/selberg-poisson-scale-moments.md) contains the dependency-closed paper proof, implementation, and verification details.
