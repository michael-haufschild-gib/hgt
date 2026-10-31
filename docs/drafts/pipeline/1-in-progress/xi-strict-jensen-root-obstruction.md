# Strict Xi Jensen root obstruction

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** A multiple root of a reversed finite Jensen section of Xi falsifies RH;
  coefficient reversal would give the ordinary-section version away from zero.

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

`infinite_positive_real_XiC_zeros` supplies the factors unconditionally. Division at
a positive zero preserves the nonzero value at the origin and leaves infinitely many
positive zeros. `iteratedDeriv_id_mul_zero` supplies the finite-section multiplication
identity without a new analytic assumption. A reversed section has degree at most `d`;
its leading coefficient is the nonzero quotient value at the origin.

## Open proof obligations

- Exact multiplicity drop for real Laguerre shifts, including degree-zero cases.
- Entire product-to-reversed-Jensen differential identity.
- Extraction of finitely many Xi real factors with a nonzero Laguerre–Pólya quotient.
- Transfer of simplicity through coefficient reversal and complete source audit.

No strictness theorem or falsification endpoint is yet claimed.
