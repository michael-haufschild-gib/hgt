# Matched–quantile rigid polar transport

## Status

Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMActualHeadMatchedQuantilePolarCoordinateTransport.lean`.
Exact module build and axiom audit pass. The declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Conjecture loop

### Failed conjecture: unsigned quantile absorption

The existing reciprocal-higher-Gamma chi-square estimate cannot be made cofinal. Its diagonal
cell cost contains a positive multiple of
`sum (Lambda(n) / sqrt(n))^2`, which diverges. This failure is intrinsic even before cross-cell
overlap.

### Pivot: compare equal-mass cells in their natural mass coordinate

Set

`Y(h) = 2 exp(h / 2)` and `H(y) = 2 log(y / 2)`.

Lean proves the exact substitution

`integral_[lo,hi] exp(h/2) G(h) dh = integral_[Y(lo),Y(hi)] G(H(y)) dy`

for every continuous profile `G`. Both a matched cell and its cumulative quantile cell then have
literal `Y`-length `Lambda(n) / sqrt(n)`. Consequently the two cells differ by one rigid
translation, not by an arbitrary endpoint deformation.

## New rigid law

Let `delta_n` be quantile lower endpoint minus matched lower endpoint in `Y`-coordinate, and let

`R_n = criticalMellinCompletedError(log n) - 2 (1 - exp(-log n/2))`.

The upper and lower endpoint displacements are identical. Moreover Lean proves

`delta_n = -R_n - (matchedUpper_n - 2 exp(log n / 2))`

and the sharp one-atom corridor

`-R_n - Lambda(n)/sqrt(n) <= delta_n <= -R_n`.

Thus completed arithmetic error is exactly the rigid transport coordinate, up to one local atom;
it is not merely an external error estimate.

## Global coverage theorem

The whole matched polar coverage seam is exactly

1. the finite sum, over physical indices, of a common-interval profile minus its rigid translate;
2. minus one terminal quantile interval.

No absolute prime mass, remote tail, overlap multiplicity, or partition premise remains. Every
finite-cell displacement in this identity satisfies the completed-error corridor above.

## Why this survives the quantile chi-square no-go

The divergent quantile diagonal cost charges variation across each cell even when its cumulative
position is perfect. Rigid matched transport charges only `delta_n`: if `delta_n = 0`, its cell
cost is exactly zero. Therefore the previous diagonal lower bound does not transfer to this
coordinate system.

## Hostile audit

- This module does not bound or sign `R_n`.
- It does not sign the rigid profile difference.
- It retains the terminal quantile interval with its actual orientation.
- It does not claim that higher Gamma energy already dominates the rigid transport sum.
- It supplies no RH conclusion by itself.

Next hard conjecture: combine the corpus de la Vallee Poussin rate for the von Mangoldt staircase
with the rigid corridor, then build a reciprocal-Gamma transport cost whose diagonal vanishes at
zero displacement and is summable at the resulting relative polar displacement scale.
