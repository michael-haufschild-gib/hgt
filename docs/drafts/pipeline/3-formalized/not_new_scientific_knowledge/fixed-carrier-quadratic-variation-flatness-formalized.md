# Fixed-carrier quadratic variation is path-flat

- **ID:** `fixed-carrier-quadratic-variation-flatness-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`
- **Paper proof:** `fixed-carrier-quadratic-variation-flatness.md`
- **Lean target:**
  `GaloisForLFunctions.HTGeometry.NestedProjectionQuadraticVariation`

## Exact theorem

For bounded operators on a real or complex Hilbert space, define
\[
\Delta_D(P,Q)=QD(P-Q)DQ.
\]
If \(QR=RQ=R\), then
\[
\Delta_D(P,R)
=\Delta_D(Q,R)+R\Delta_D(P,Q)R.
\tag{1}
\]
Therefore any two operators \(Q_1,Q_2\) absorbed by the same final carrier \(R\) give
\[
\Delta_D(Q_1,R)+R\Delta_D(P,Q_1)R
=
\Delta_D(Q_2,R)+R\Delta_D(P,Q_2)R.
\tag{2}
\]
No projection, self-adjointness, or intermediate-comparability hypothesis is required for
`(1)`--`(2)`.

When \(P,Q\) are nested orthogonal projections and \(D=D^\dagger\), the layer \(P-Q\) is an
orthogonal projection and
\[
\Delta_D(P,Q)
=\bigl((P-Q)DQ\bigr)^\dagger\bigl((P-Q)DQ\bigr).
\tag{3}
\]
It is exactly the restriction defect of the off-carrier corner
\[
C_D(P)=PD(1-P)DP:
\qquad
C_D(Q)-QC_D(P)Q=\Delta_D(P,Q).
\tag{4}
\]
Finally, ordinary triple curvature is only compression curvature:
\[
\Delta_D(P,R)-\Delta_D(P,Q)-\Delta_D(Q,R)
=R\Delta_D(P,Q)R-\Delta_D(P,Q).
\tag{5}
\]

For orthogonal projections \(Q,R\), the unit-top, unit-passage cocycle gives the converse:
\[
\Delta_I(I,R)
=\Delta_I(Q,R)+R\Delta_I(I,Q)R
\quad\Longleftrightarrow\quad
QR=RQ=R.
\tag{6}
\]
Thus one universal quadratic test detects whether \(R\) is genuinely a common absorbed future
carrier.

## Mathematical delta

The paper conjectured path-flatness for nested projection diamonds. Formalization exposed the
stronger invariant: fixed-carrier flatness follows from the two final absorption identities alone.
Branching, noncommuting intermediate operators, and loss of intermediate positivity do not evade
the no-go. Equation `(6)` supplies the converse finite discriminator: cocycle flatness is
equivalent to common-future absorption in the orthogonal-projection model.

The positive survivor is `(3)`--`(4)`: shrinking a coherent carrier creates an exact positive Gram
record. The representation lesson is sharp:

```text
one globally supplied carrier
  -> transported quadratic variation is endpoint-exact;

nonzero force curvature
  -> local carriers or their comparison maps must themselves be source-generated
     and fail compatible globalization.
```

## Lean certificate

Module:
`formal/GaloisForLFunctions/HTGeometry/NestedProjectionQuadraticVariation.lean`.

Principal declarations:

- `nestedProjectionLostLayer_mul_self`;
- `nestedProjectionOffCarrierCorner_restrictionDefect`;
- `nestedProjectionQuadraticVariation_eq_adjoint_mul`;
- `nestedProjectionQuadraticVariation_compressed_cocycle`;
- `nestedProjectionQuadraticVariation_diamond_flat`; and
- `nestedProjectionQuadraticCurvature_eq_compression_sub_self`;
- `projection_absorption_of_compression_eq_self`; and
- `nestedProjectionQuadraticVariation_unit_flat_iff_absorption`.

Direct foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/NestedProjectionQuadraticVariation.lean
```

completed with exit code zero and no warnings.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.NestedProjectionQuadraticVariation
✔ [3084/3084] Built GaloisForLFunctions.HTGeometry.NestedProjectionQuadraticVariation
Build completed successfully (3084 jobs).
```

The axiom audit reports only Mathlib's standard logical quotient infrastructure:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration occurs in the module.

## Hostile scientific audit

This is a standard algebraic bridge, not a physical discovery. It does not identify projections
with quantum possibilities or Gram squares with spacetime. It proves that a broad proposed
mechanism cannot produce force, then isolates the missing type of structure.

The next exact conjecture must define source-generated comparison between changing local carriers.
Merely replacing projections by arbitrary fixed-carrier operators cannot work because `(2)` already
covers that escape.
