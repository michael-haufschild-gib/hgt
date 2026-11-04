# Cross-load scaling capacity at scale eight

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Result:** The fixed origin-and-scale-seven cross-load fails at scale eight.
  Its scalar multiples have an exact admissibility boundary strictly between
  one half and one.

Let `x₈=½log(8/π)`, `H= nativeShiftedMatrix 5 0 x₈`,
`G=thetaCuspCenterCompensationSource x₈`, and
`B=loadMapᵀ paidSevenSchur loadMap`. There is `1/2<τ<1` such that, for every real `t`,

- `H+tGB` is positive definite iff `t<τ`;
- `H+tGB` is positive semidefinite iff `t≤τ`;
- `H+τGB` is singular.

In particular, the half-load is positive definite and the unit-load is not
positive semidefinite. This classifies scaling at one source point; global
rank-nine positivity remains open.

## Proof

Normalize by the positive first-pair amplitude and the invertible Gaussian
basis. The complete native form differs from the leading-pair form at the
rational weight `37751346/10¹⁸` by at most `1/10` times the identity.
The unequal-pair weight error contributes at most `1/20`, the remaining
unequal pairs and infinite tail contribute `147/4000`, and the second and
third pure atoms contribute at most `1/100` together.

The first-atom mass and derivative bounds, with
`14/15≤2x₈≤187/200`, enclose the complete normalized compensation between
explicit negative rationals. Exact Schur certificates prove positivity of
the resulting half-load lower matrix and a negative direction for the
unit-load upper matrix. All polynomial moments and load entries are identified
with the actual source.

Since `G<0` and `B≥0`, the pencil decreases with `t`. Its positive set is open,
downward closed, contains `1/2`, and is bounded above by `1`. Its supremum is
positive semidefinite by continuity and singular by openness. Any larger
semidefinite parameter would make the boundary strictly positive by convex
interpolation with the positive native form at `t=0`, a contradiction.

## Lean

Under `GaloisForLFunctions.ThetaCuspSections`:

- `EightCrossSource.source_half_load_posDef`
- `EightCrossSource.crossRepair_not_posSemidef`
- `EightCrossCapacity.exact_scaling_capacity`
- `EightCrossCapacity.source_boundary`

Modules: `FifthEvenScaleEightData`, `FifthEvenScaleEightSourceBounds`,
`FifthEvenScaleEightCapacity`. The complete-source and capacity declarations
pass the transitive axiom audit with only `propext`, `Classical.choice`, and
`Quot.sound`.
