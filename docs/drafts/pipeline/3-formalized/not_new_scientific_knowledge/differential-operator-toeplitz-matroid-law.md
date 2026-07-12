# Differential-operator Toeplitz matroid law

- **ID:** `differential-operator-toeplitz-matroid-law`
- **Stage:** 3-formalized
- **Type:** DIFFERENTIAL-ALGEBRAIC RANK BRIDGE
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [STANDARD PARENT THEORY]`
- **Statement:** Let `x` be a finite differentially algebraically independent family over a field
  of constants `C`, and let `L` be a finite matrix over `C[D]`.  The output family `L(D)x` is
  differentially algebraically independent over `C` if and only if the rows of `L` are linearly
  independent over `C[D]`.

## Exact law

For every finite output index type `I` and source index type `K`, Lean proves

```text
DifferentialIndependent C (L(D)x)
  <-> LinearIndependent C[D] (rows L).
```

The forward direction says that every polynomial operator-row circuit becomes a differential
linear circuit among the outputs.  The reverse direction says that no further nonlinear
differential circuit appears.  Thus the complete differential-independence matroid of a finite
operator-image family is exactly its polynomial operator-row matroid.

## Toeplitz proof mechanism

For a finite packet of output jets, multiplication of an operator row by `D^n` produces a finite
Toeplitz coefficient matrix on a bounded source-jet rectangle.  A constant linear relation among
these shifted rows can be regrouped into a polynomial relation among the original rows.  Polynomial
row independence therefore gives ordinary row independence of every Toeplitz packet.  Full-row-rank
linear forms preserve algebraic independence, so every finite packet of output jets is algebraically
independent.

Conversely, differential independence makes every finite source-jet rectangle linearly independent
over `C`.  Expanding a differential linear relation coefficientwise forces every polynomial
operator coefficient to vanish.  Applying this to a putative row relation proves the reverse
implication.

## Lean realization

`GaloisForLFunctions.HTGeometry.DifferentialOperatorToeplitzRank` proves, among its supporting
lemmas:

- `operatorToeplitzMatrix_rows_linearIndependent`;
- `differentialIndependent_differentialOperatorRows`;
- `differentialOperatorApplications_coefficients_eq_zero`;
- `differentialIndependent_differentialOperatorRows_iff`.

The module builds in the project toolchain.  Axiom inspection of the three principal theorems
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This theorem closes the abstract nonlinear-rank lemma used by the facet-sewn Herglotz realization.
It does not by itself identify the facet restriction-row span with the localized
Stanley--Reisner quotient, nor assemble the concrete upper-end prime-log source and structural
translation operators.  Those are separate obligations of the Stage 2 realization card.

## Gates

- [x] complete paper proof
- [x] complete unconditional Lean formalization
- [x] exact independence equivalence, not only one direction
- [x] no independent novelty claim
