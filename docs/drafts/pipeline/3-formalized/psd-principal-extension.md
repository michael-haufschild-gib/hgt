# Positive principal face extension

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [LEAN PROVED] [ABSTRACTED]`

Source: Proposition 2.3 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Exact claim

Every finite positive semidefinite matrix extends to a disjoint larger index type by a zero block.
The original matrix is recovered exactly as a principal submatrix and the trace is unchanged.
Every matrix effect `0 ≤ E ≤ 1` likewise extends by zero; its complement is `(1-E) ⊕ 1`, so
both effect inequalities remain positive semidefinite.

This is the reusable linear-algebraic content of state/effect face-surjectivity, abstracted away from
the source paper's particular context-complex definitions.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/PSDPrincipalExtension.lean`, declarations
`PSDMatrix.zeroExtend_principal`, `PSDMatrix.zeroExtend_trace`, and
`MatrixEffect.zeroExtend_principal`. Positivity is intrinsic to `PSDMatrix` and `MatrixEffect`; the
theorems introduce no axioms.
