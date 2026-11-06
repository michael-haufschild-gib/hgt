# W4 — a split Weil-group model

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `WeightFamilies/InvariantForms.lean`; the Golden invariant-weight obstruction.
- **Question:** Does compatibility between Frobenius and full `SL₂` monodromy exclude the Golden spectrum before any global trace identity is supplied?

## Candidate classification

Let `W = SL₂(ℂ) × ℤ`, with degree map the second projection. For `c ≠ 0`, the matrix representation is `R_c(g,n) = c^n g`. Its degree-zero image is all of `SL₂(ℂ)`. Every degree-one matrix has determinant `c²`, and every matrix of determinant `c²` occurs. On invariant forms of degree `m`, its action is `c^(nm)`.

For `c=√5`, the degree-one element `(diag(φ,φ⁻¹),1)` has the Golden Frobenius spectrum. Thus the countermodel should admit a full group extension and Frobenius compatibility, not merely isolated invariant-weight identities.

## Proof target

The scalar factor commutes with matrices, so `R_c` is a homomorphism. The kernel of degree is the first factor. For determinant `c²`, the inverse construction is `A ↦ (c⁻¹A,1)`. The invariant action follows from multilinearity and determinant-one invariance.

This is an abstract group model. It supplies no étale or analytic arithmetic base, topology comparison, global Euler product, or cohomological trace formula. Those cannot be inferred from the extension alone. Lean formalization remains pending.
