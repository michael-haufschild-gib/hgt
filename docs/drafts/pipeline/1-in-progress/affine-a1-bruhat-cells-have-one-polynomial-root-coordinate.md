# Affine A₁ Bruhat cells have one polynomial root coordinate

- **Stage:** 1-in-progress
- **Parent:** [Elliptic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** Refine the actual affine Bruhat decomposition into unique finite
  root coordinates for right Borel cosets, then identify the arithmetic cells.

## Mechanism

The audited inversion intervals in `AffineA1Roots` lie entirely in one of
`α+nδ` or `−α+nδ`. Their root subgroups therefore share one matrix entry and
commute. A cell needs one finite polynomial upper or lower parameter.

For a translation `diag(X^m,X^−m)`, upper–diagonal–lower factorization isolates
upper degrees `0,…,2m−1` when `m≥0`; lower–diagonal–upper factorization isolates
lower degrees `1,…,−2m` when `m<0`. Split at the corresponding conjugation
threshold. The finite head supplies the cell coordinate, while its tail
and the other factors lie in the conjugated-Iwahori intersection. Uniqueness reduces to vanishing of a finite polynomial
whose shifted parameter lies in the required positive-series ideal.

Right cosets in `B w B/B` use `I(w⁻¹)`. Representatives `u w⁻¹`, indexed by
`I(w)`, must be used when matching the existing Weyl-sum convention.

Over the actual countable elliptic function field, finite polynomial coordinates
have one common finite set of bad places. Their representatives and the Weyl
lifts lie in the restricted arithmetic group. The remaining Borel factor then
lies there by group closure. Finite-dimensional cell coordinates would prove
countability of the actual arithmetic coset set.

## Status

Inversion intervals, both Iwahori Gauss factorizations and unique Weyl double-coset
labels are audited. The polynomial refinement, uniqueness and arithmetic
restriction statements remain conjectures requiring proofs and Lean audits.
