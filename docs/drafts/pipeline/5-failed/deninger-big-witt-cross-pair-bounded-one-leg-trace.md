# Deninger Big-Witt bounded one-leg trace

- **ID:** `deninger-big-witt-cross-pair-bounded-one-leg-trace`
- **Stage:** 5-failed
- **Type:** SHARP NO-GO WITH POSITIVE SURVIVOR
- **Route:** L
- **RH used:** no
- **Computation used:** no

## Attempt

Extend finite right-edge coordinate summation to a continuous linear
functional on the actual ordered-edge Calderón packet completion
`ell^2(I,C)`. Use that bounded functional as the cofinal one-leg contraction
of the coherent four-label Frobenius source.

## Exact obstruction

No such continuous functional exists. Normalized indicators of `N` distinct
packet coordinates have Hilbert norm one and coordinate sum `sqrt N`.
Moreover the uniform averages of the first `N+1` coordinates converge to zero
in the packet Hilbert norm while their coordinate sum stays exactly one.
Thus algebraic summation is sequentially nonclosable, not merely unbounded.

## Positive survivor

The algebraic trace on finite-support packets is canonical and factors the
actual coherent Frobenius fiber exactly:

```text
FiberCoefficient_(p,q)(S) = (-2 L_pq) Sigma(R_S).
```

This identifies required transport as a singular source-domain problem.
Surviving route must construct a Xi/Green-derived renormalized graph domain
or a different topology before completion. It cannot claim a bounded or
closed extension on standard `ell^2`, and it cannot discard right-edge
provenance by projecting immediately to one Gamma witness.

## Lean status

Formalized in
`DeningerBigWittFrobeniusCrossPairSingularOneLegTrace.lean`; capstones
`deningerBigWittCrossPairAlgebraicOneLegTrace_noContinuousExtension` and
`deningerBigWittCrossPairAlgebraicOneLegTrace_not_closable`.
