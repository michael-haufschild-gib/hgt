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

## Proof route

Each radical is an eigenvector for the full kernel `Gal(L/D)` with its
quadratic sign character. Two characters coincide exactly when the ratio
of their radicals is fixed by the whole kernel, hence belongs to `D`;
this is exactly equality of their radicand square classes.
Distinct multiplicative characters are linearly independent. Applying every
kernel automorphism to a relation therefore forces each character component
to vanish separately. Conjugation separates the source-field ordinate sum
from the purely imaginary offsets.

## Boundary

The actual square-class partition and the relations inside its classes
remain to be determined. These are constraints on the full divisor, not a
claim of rational independence or a proof of RH.
