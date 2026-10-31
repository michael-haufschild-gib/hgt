# Affine A₁ Bruhat cells have one polynomial root coordinate

- **Stage:** 1-in-progress
- **Parent:** [Elliptic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** Refine the actual affine Bruhat decomposition into unique finite
  root coordinates for right Borel cosets, then identify the arithmetic cells.

## Mechanism

The audited inversion intervals in `AffineA1Roots` lie entirely in one of
`α+nδ` or `−α+nδ`. Their root subgroups therefore share one matrix entry and
commute. A cell needs one finite polynomial upper or lower parameter.

For a positive translation, the lower–diagonal–upper Iwahori Gauss decomposition
isolates the lower parameter. Split it at the conjugation threshold; its finite
head supplies the cell coordinate, while its tail and the other two factors
lie in the conjugated-Iwahori intersection. The opposite Gauss decomposition
handles the upper string. Uniqueness reduces to vanishing of a finite polynomial
whose shifted parameter lies in the required positive-series ideal.

Right cosets in `B w B/B` use `I(w⁻¹)`. Representatives `u w⁻¹`, indexed by
`I(w)`, must be used when matching the existing Weyl-sum convention.

Over the actual countable elliptic function field, finite polynomial coordinates
have one common finite set of bad places. Their representatives and the Weyl
lifts lie in the restricted arithmetic group. The remaining Borel factor then
lies there by group closure. Finite-dimensional cell coordinates would prove
countability of the actual arithmetic coset set.

## Status

Inversion intervals, full Iwahori Gauss coordinates and unique Weyl double-coset
labels are audited. The polynomial refinement, uniqueness and arithmetic
restriction statements remain conjectures requiring proofs and Lean audits.
