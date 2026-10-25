# Diagonal power laws do not determine mixed homogeneity

- **ID:** biarithmetic-diagonal-to-mixed-homogeneity
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md).
- **Retired implication:** exact power-law diagonals, cyclicity, positivity, the cofactor radius bound, and critical packet contraction force a homogeneous mixed kernel or its stronger packet contraction.

## Exact obstruction

The cyclic rank-three metric model in
[Diagonal scaling and stationary repair](../3-formalized/biarithmetic-diagonal-scaling-countermodel.md)
satisfies every listed premise, but `K(1,2)=1/6` and `K(2,4)=0`. Its mixed-vector energy
also violates quarter-contraction under dilation 2. No numerical approximation is involved.

## Positive survivor and new insight

The same cyclic dilation representation admits an explicit positive stationary metric,
obtained by averaging its three conjugate metrics. Its kernel is fully homogeneous and
preserves every original diagonal. Thus diagonal data leave stationarity undetermined even
when all finite packet contraction constraints hold. The positive result includes the exact
representation, spanning vectors, metric bounds, all packet bounds, and stationary repair.

Paper proof is dependency-closed. Lean module
`GaloisForLFunctions/BiarithmeticGeometry/DiagonalScalingCountermodel.lean` passes its direct
check; all main declarations have only `propext`, `Classical.choice`, `Quot.sound` in their
transitive axiom closures. The stage-3 card lists the exact theorem names.

## Boundary of the no-go

This is a calibration countermodel, not an actual Möbius escape state and not a claimed
regularly varying scalar source. A3 for the actual receiver remains open. A stationary
average of a family of tangents need not be one source subsequence limit; that realization
problem is also open. The model is multiplicative and makes no Class III cancellation claim.
