# Finite-dimensional affine unitary rigidity

- **ID:** biarithmetic-finite-unitary-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), A4 and finite affine representation theory.
- **Statement:** A continuous finite-dimensional unitary family `U_t` with `U_0=1` and invertible dilation covariance `D U_t=U_(pt) D`, for `p>1`, is identically the identity. No translation group law is needed.

## Dependency-closed paper proof

Conjugacy and cyclicity of trace give `tr(U_t)=tr(U_(t/p))`. Iteration gives equality with
`tr(U_(t/p^k))`. Since `p>1`, continuity at zero implies `tr(U_t)=tr(1)`.
For a unitary matrix `U`,

`tr((U-1)* (U-1))=2n-tr(U)-conjugate(tr(U))`.

Here `*` denotes conjugate transpose of the first factor. The displayed value is zero when
`tr(U)=n`. It is also the sum of the squared absolute values of all entries of `U-1`, so
every entry vanishes. Thus `U=1`.

## Positive classification and limits

The full finite-dimensional unitary family is classified: translations are trivial, and any
invertible dilation is compatible with that trivial family. This is stronger than ruling out
one candidate action. It pinpoints three requirements for a nontrivial translation limit:
either infinite dimension, failure of unitarity, or failure of invertible dilation covariance.

The theorem does not assert that actual moving translations exist, are unitary, survive
normalization, or have invertible dilations. It is classical representation-theoretic
calibration, with no claim of arithmetic selectivity or new cancellation.

## Verification

- [x] Dependency-closed paper proof.
- [x] Complete scratch proof checked by Lean for every real `p>1`.
- [x] Direct leaf check.
- [x] Transitive axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

Module: `GaloisForLFunctions/BiarithmeticGeometry/FiniteAffineUnitaryRigidity.lean`.
Main declaration: `finite_affine_unitary_rigidity`.
