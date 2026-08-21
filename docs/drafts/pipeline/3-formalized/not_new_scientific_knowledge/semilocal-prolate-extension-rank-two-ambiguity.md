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

## Lean formalization — COMPLETE

Module: `formal/GaloisForLFunctions/RHTower/JacobiDeficiencyRankTwoAmbiguity.lean`
(wired into `GaloisForLFunctions.RHTower`; `#print axioms` gives exactly
`propext, Classical.choice, Quot.sound` on every capstone).

| Card item | Lean declaration |
|---|---|
| the formal half-line Jacobi recurrence with its left boundary equation | `IsJacobiSolution` |
| "a solution is determined by its first value and the fixed left boundary equation" | `IsJacobiSolution.ext` |
| the solution space at a spectral parameter | `jacobiSolutions` |
| "deficiency index at most one in each half-plane" | `rank_jacobiSolutions_le_one` |
| complex conjugation commutes with the real formal matrix | `IsJacobiSolution.conj` |
| the deficiency space (square-summable solutions) | `sqSummable`, `jacobiDeficiency`, `rank_jacobiDeficiency_le_one` |
| conjugation maps `ker(J*−z)` onto `ker(J*−z̄)` | `mem_jacobiDeficiency_conj` |
| `(1)` the indices are `(0,0)` or `(1,1)` | `jacobiDeficiency_eq_bot_iff_conj`, `jacobi_deficiency_indices` |
| equal indices give a self-adjoint extension | `exists_isSelfAdjoint_extension_of_deficiency_one` |
| the parity direct sum has rank at most two | `hasRankLE_add` (with `hasRankLE_neg`, `hasRankLE_sub`) |
| "finite-rank operators belong to every Schatten ideal, so ideal membership is unchanged" | `memSchattenClass_congr_of_hasRankLE` |
| the two-block statement in full | `memSchattenClass_congr_of_two_block` |

Proof mechanisms, all unconditional:

1. **Deficiency index ≤ 1.** `IsJacobiSolution.ext` runs a two-step induction: the boundary equation
   fixes `u₁` from `u₀` (dividing by `a₀ ≠ 0`), and `step n` fixes `u_{n+2}` from `(u_n, u_{n+1})`.
   Evaluation at index `0` is therefore an injective linear map from the solution space to `ℂ`, so
   `Module.rank ℂ ≤ 1` — this is the card's "a solution of the second-order recurrence is determined
   by its first value and the fixed left boundary equation".
2. **Equality of the indices.** The coefficients are real, so `conj` carries a solution at `z` to a
   solution at `conj z`, and `‖conj u_n‖ = ‖u_n‖` preserves square-summability. Applying this in both
   directions (`Complex.conj_conj`) gives `jacobiDeficiency z = ⊥ ↔ jacobiDeficiency (conj z) = ⊥`,
   and at `z = i` (`Complex.conj_I`) this is exactly the `(0,0)`-or-`(1,1)` alternative. Only the
   *triviality* of the two spaces is compared, which is all that is needed given the rank bound —
   no antilinear-dimension theory is required.
3. **Existence of a self-adjoint extension.** `exists_isSelfAdjoint_extension_of_deficiency_one`
   packages the corpus's von Neumann boundary construction
   (`LinearPMap.deficiencyExtension_isSelfAdjoint` in `HTGeometry.VonNeumannDeficiency`) at the unit
   boundary parameter `u = 1`.
4. **The rank-two ambiguity is Schatten-invisible.** `hasRankLE_add` proves ranks add (the sum of two
   ranges lies in `V ⊔ W`, whose `finrank` is at most `finrank V + finrank W`), so a parity-preserving
   change of extension moves the corner by an operator of rank at most two. Writing
   `B = A + (B − A)` and using the corpus's Schatten additivity
   (`GaloisForLFunctions.HTGeometry.memSchattenClass_add`) together with
   `memSchattenClass_of_hasRankLE` gives membership in *both* directions, i.e. an `iff` — the card's
   `[PROVED]` route consequence that "Schatten membership of a relative-resolvent corner, if proved
   for one parity-preserving extension, is stable under all boundary choices".

The card's two `[OPEN CORE]` items — deriving the limit-point/limit-circle alternative and the
boundary condition from semilocal support/Fourier/Sonin data, and proving invariance of the
determinant boundary under the rank-two ambiguity — are explicitly not part of the stated theorem
and are untouched. The Fredholm-determinant caveat (a rank-two correction *can* change it) is the
reason no determinant statement is claimed here.
