# W4 — a split Weil-group model

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `WeightFamilies/InvariantForms.lean`; the Golden invariant-weight obstruction.
- **Statement:** An abstract group extension with full `SL₂` image realizes every prescribed-determinant Frobenius, including the Golden countermodel.

## Exact classification

Let `W = SL₂(ℂ) × ℤ`, with degree map the second projection. For `c ≠ 0`, the matrix representation is `R_c(g,n) = c^n g`. Its degree-zero image is all of `SL₂(ℂ)`. Every degree-one matrix has determinant `c²`, and every matrix of determinant `c²` occurs. On invariant forms of degree `m`, its action is `c^(nm)`.

Every group element normalizes the degree-zero image: conjugation preserves the degree, and the representation intertwines the two actions. For `c=√5`, Golden Frobenius has a degree-one lift. The countermodel therefore admits a group extension and Frobenius compatibility, not merely isolated invariant-weight identities.

## Proof

The scalar factor commutes with matrices, so `R_c` is a homomorphism. The kernel of degree is the first factor, whose image is exactly the determinant-one matrices. For determinant `c²`, the inverse construction is `A ↦ (c⁻¹A,1)`. Conjugating a degree-zero lift by `g` gives the required intertwiner for `R_c(g)`. The invariant action follows from multilinearity and determinant-one invariance. Golden Frobenius has determinant `5=(√5)²`, so the degree-one classification supplies its lift.

## Lean

Module: `ArithmeticKunnethTheory/WeightFamilies/SplitWeilModel.lean`.

- `splitAction`, `splitDegree_surjective`: the representation and integer quotient.
- `splitAction_degree_zero_iff`, `splitAction_degree_one_iff`: exact image classifications.
- `splitAction_normalizes`, `splitAction_invariant`: Frobenius compatibility and invariant characters.
- `goldenFrobenius_has_split_lift`: the impure degree-one example.

Checked with `lake --old env lean`. This is an abstract group model. It supplies no étale or analytic arithmetic base, topology comparison, global Euler product, or cohomological trace formula. Those cannot be inferred from the extension alone.
