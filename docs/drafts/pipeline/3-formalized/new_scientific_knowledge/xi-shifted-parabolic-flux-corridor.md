# Xi-shifted parabolic flux corridor

Status: formalized in Lean 4

Novelty: `[NOVELTY-PLAUSIBLE]` within corpus; external literature audit not yet performed for this
exact shifted-Xi Jacobi-source formulation.

## New theorem package

Module:
`GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFluxCorridor`

The corpus had two separate laws:

1. a degree-uniform pointwise floor
   `1/4 < w^4 * adaptiveMixedCompletedSourceAction(w,n)`;
2. an exact identity equating cumulative Jacobi flux at mass `a` with the entire future integral of
   this source action.

The new module proves their missing transport:

- physical-mass source floor `1/(4*y^2) < sourceAction(sqrt y,n)`;
- tail-integrated capital law `1/(4*a) ≤ cumulativeJacobiFlux(a,n)`;
- automatic version strictly beyond block terminal frontier `T_(n+2)`;
- diagonal, degree-uniform dimensionless floor
  `1/4 ≤ dimensionlessCumulativeJacobiFlux(w,n)`.

Last statement holds above one universal mass threshold for every `n ≥ 2` whenever
`T_(n+2) < w^2`; no fixed-degree limit or prescribed mass-degree schedule is used.

## Significance and boundary

This closes an order-of-limits gap: fixed-degree arcsine recession cannot itself control arbitrary
degree-mass diagonals, while integrated literal source action does. It gives source-capital
noncollapse on every actual terminal positive ray.

It does not prove RH. Existing reciprocal-clock upper bounds leave a wide compatible corridor, and
fixed-degree arcsine recession predicts a larger limiting flux. A contradiction still needs a
stronger degree-uniform lower capital law, a cross-degree transport law, or an RH-sensitive upper
bound.

## Verification

- Direct source check:
  `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFluxCorridor.lean`
- Exact target build only:
  `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFluxCorridor`
- Axiom audit for all four public theorems:
  `[propext, Classical.choice, Quot.sound]`
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella not built.
