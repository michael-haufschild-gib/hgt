# Strict Xi Jensen root obstruction

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** A nonzero multiple root of a finite Jensen polynomial of Xi falsifies RH.

## Proposed mechanism

The corpus supplies RH-to-Laguerre–Pólya membership, division by real zeros
(`laguerrePolya_dslope`), Jensen reversal as a differential operator
(`diffOpApply_X_pow`), and Hermite–Poulain preservation.

For a split real polynomial, a multiple root of `p'-a p` must be an inherited root
of `p` with one greater multiplicity. Repeated application therefore makes a
degree-at-most-`d` polynomial squarefree after `d` nonzero real linear factors.
Factor `d` nonzero real zeros from Xi; the quotient remains Laguerre–Pólya.
Apply those factors as differential operators to the quotient's reversed Jensen
section. Coefficient reversal preserves simplicity away from zero.

## Open proof obligations

- Exact multiplicity drop for real Laguerre shifts, including degree-zero cases.
- Entire product-to-reversed-Jensen differential identity.
- Extraction of finitely many Xi real factors with a nonzero Laguerre–Pólya quotient.
- Transfer of simplicity through coefficient reversal and complete source audit.

No strictness theorem or falsification endpoint is yet claimed.
