# A positive prefix gives the exact complete-Weil Schur reduction

- **ID:** a-positive-prefix-gives-the-exact-schur-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; actual coordinate compression.
- **Statement:** For every sufficiently large prefix length `M`, simultaneously for all
  `N≥M` and `c>0` with `cM≤N`, the actual plateau prefix is positive definite and
  complete-matrix positive semidefiniteness is equivalent to its actual Schur complement.

## Proof

Compress the complete length-`N`, overlap-`c` matrix to coordinates `1..M`.
Its atom width remains `c/N=(cM/N)/M`, and the literal normalized pairing therefore
equals the complete length-`M` matrix at overlap `cM/N`.
The explicit plateau's conductor-one margin exceeds `1/20`. The existing uniform
touching theorem supplies a common eventual eigenvalue floor `1/25` for every overlap
in `(0,1]`. It consequently proves positivity of this prefix whenever `cM≤N`.

Split coordinates into the prefix and its complement. The actual matrix is, up to this
coordinate equivalence, `[[D,B],[B*,A]]`, where all prime, Gamma, and polar entries are retained.
Since `D` is proved positive definite, the exact block theorem gives
`complete matrix PSD ↔ A-B*D⁻¹B PSD`. The eliminated cost `B*D⁻¹B` is positive semidefinite.
No invertibility or prefix-positivity assumption is added to the final eventual theorem.

This supplies a genuine coordinate block and an exact residual obligation. It does not
identify the additive-neighbour edges with a coordinate block or prove the residual sign.

## Lean verification

Module: `GaloisForLFunctions/TransMetzlerWeilPositivity/APositivePrefixGivesTheExactSchurReduction.lean`.
Main declarations: `plateauPrefixBlock_eq`, `eventually_plateauPrefixBlock_posDef`,
`completeWeilMatrix_prefix_blocks`, `eventually_completeWeil_posSemidef_iff_prefixSchur`,
and `eventually_plateauPrefixSchur_cost_posSemidef`.

Direct `lake --old env lean` check passed with default limits and no warnings.
All four transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by the TransMetzlerWeilPositivity umbrella.
