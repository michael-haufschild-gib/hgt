# Arithmetic splitting of additive zero-width relations

- **ID:** galois-zero-additive-width-relations
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Questions:** Additive relations among actual zeros; arithmetic invariants.

Let `K` be the complete-fibre source, `L` the centered zero field,
`D=K(δ_q² : all q)`, and `b_q=iδ_q` for nonzero widths.
Declare `q∼r` when `−δ_q²` and `−δ_r²` have the same square class in `D`.

## Target

Every finite `D`-linear relation among the `b_q` splits into separate
relations within the classes `q∼r`. A family of these radicals is
`D`-linearly independent exactly when its square classes are pairwise distinct.
Within one class all radicals differ by a nonzero scalar in `D`.

Apply this decomposition to all integer relations among centered spectral
zeros `w_q=t_q+b_q`, with no height cutoff: the ordinate sum must vanish,
and the offset sum must vanish separately in each arithmetic square class.
This constrains rational relations without assuming independence of zero
ordinates or widths.

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

## Boundary

The actual square-class partition and the relations inside its classes
remain to be determined. These are constraints on the full divisor, not a
claim of rational independence or a proof of RH.
