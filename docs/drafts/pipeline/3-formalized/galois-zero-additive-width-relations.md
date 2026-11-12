# Arithmetic splitting of additive zero-width relations

- **ID:** galois-zero-additive-width-relations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Additive relations among actual zeros; arithmetic invariants.

Let `K` be the complete-fibre source, `L` the centered zero field,
`D=K(δ_q² : all q)`, and `b_q=iδ_q` for nonzero widths.
Declare `q∼r` when `−δ_q²` and `−δ_r²` have the same square class in `D`.

## Theorem

Every finite `D`-linear relation among the `b_q` splits into separate
relations within the classes `q∼r`. A family of these radicals is
`D`-linearly independent exactly when its square classes are pairwise distinct.
Within one class all radicals differ by a nonzero scalar in `D`.

For every finitely supported integer family on the complete centered zero
divisor,

```
∑ n_q w_q = 0  ↔  ∑ n_q t_q = 0 and ∀ C, ∑_(q∈C) n_q b_q = 0.
```

Here `w_q=t_q+b_q`, and `C` ranges over nonzero arithmetic width classes.
Zero offsets contribute nothing. Multiplicities are retained, and no height
cutoff or independence assumption is imposed.

## Paper proof

Each radical is an eigenvector for the full kernel `Gal(L/D)` with its
quadratic sign character. Two characters coincide exactly when the ratio
of their radicals is fixed by the whole kernel, hence belongs to `D`;
this is exactly equality of their radicand square classes.
For a finite relation, apply every kernel automorphism. Group the resulting
identity by the distinct multiplicative characters. Dedekind independence
forces each grouped coefficient to vanish. Conversely, summing the zero
components recovers the relation. Zero radicals contribute nothing, so this
also covers every divisor copy on the critical line.

For distinct classes, each component of a relation has a single nonzero
radical, forcing its coefficient to vanish. Equal classes give proportional
radicals and hence a dependence.

Write each centered zero as `w_q=t_q+b_q`. Conjugation fixes all coefficients
in `D` and all `t_q`, while negating every `b_q`. Adding and subtracting a
relation and its conjugate separates its ordinate and offset parts. Apply
the class decomposition to the offset part. Specializing coefficients to
integers gives the exact equivalence for the entire centered zero divisor.

## Formalization

`GaloisTheoryOfZeros/TheArithmeticClassesOfAdditiveZeroRelations.lean`:
`sourceRootSign_eq_iff_square`, `radical_relation_iff_nonzero_square_components`,
`sameWidthSquareClass_equivalence`, `sameWidthSquareClass_iff_proportional`,
`widthRadicals_linearIndependent_iff`, `zeroOffset_relation_iff_square_components`,
`centeredZero_relation_iff_arithmetic_components`, and
`centeredZero_integer_relation_iff`.

Direct source audit passed. Eleven transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Boundary

The actual square-class partition and the relations inside its classes
remain to be determined. These are constraints on the full divisor, not a
claim of rational independence or a proof of RH.
