# Semilocal prolate extension and rank-two ambiguity

- **ID:** semilocal-prolate-extension-rank-two-ambiguity
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXTENSION-THEORY BRIDGE (paper)
- **Scientific status:** NOT NEW SCIENTIFIC KNOWLEDGE
- **Source input:** the real parity-block Jacobi matrices of the formal semilocal prolate operator

## Statement

For every finite prime set `P` and `lambda>0`, the minimal symmetric operator defined by the formal
semilocal prolate Jacobi matrix has a self-adjoint extension.

On each Fourier-parity block, the deficiency indices are either

`(0,0)` or `(1,1)`.                                         (1)

In the first case the block is essentially self-adjoint. In the second, its self-adjoint extensions
form the usual one-parameter boundary family, and the resolvents of any two extensions differ by rank
one. For the direct sum of the two parity blocks, resolvents of any two parity-preserving self-adjoint
extensions differ by rank at most two.

Consequently, once a single extension has a relative-resolvent corner in a Schatten ideal, every
parity-preserving extension has a corner in the same ideal. However a Fredholm determinant or scalar
boundary may change by a rank-two perturbation factor and is not canonical until the source selects
the boundary condition.

## Proof

The source parity blocks are real symmetric half-line Jacobi matrices with nonzero off-diagonal
coefficients. The minimal Jacobi operator on finitely supported sequences has deficiency index at most
one in each half-plane: a solution of the second-order recurrence is determined by its first value and
the fixed left boundary equation.

Complex conjugation commutes with the real formal matrix and maps

`ker(J_min^*-i)` antiunitarily onto `ker(J_min^*+i)`.

Thus the two deficiency indices are equal and at most one, proving (1). Equality of the deficiency
indices is exactly the criterion for existence of self-adjoint extensions.

If the indices are `(1,1)`, the abstract Krein resolvent formula says that the difference of the
resolvents of two self-adjoint extensions has rank at most the deficiency index, hence rank one. The
direct sum of the two parity blocks gives rank at most two.

Finite-rank operators belong to every finite Schatten ideal, so ideal membership is unchanged when
the extension is changed. Fredholm determinants are multiplied by the determinant of a finite-rank
correction, which can be nontrivial and boundary-parameter dependent.

## Route consequence

- `[PROVED]` Bare self-adjoint-extension existence is not the Route B obstruction.
- `[PROVED]` Schatten membership of a relative-resolvent corner, if proved for one parity-preserving
  extension, is stable under all boundary choices.
- `[OPEN CORE]` Determine the limit-point/limit-circle alternative and derive a boundary condition
  from semilocal support/Fourier/Sonin data.
- `[OPEN CORE]` Prove that the desired determinant boundary is invariant under the rank-two resolvent
  ambiguity, or show that source compatibility selects one extension.

## Novelty audit

These are standard half-line Jacobi and Krein extension theorems applied to the source matrix. They
clarify the exact boundary ambiguity but are not new scientific knowledge.
