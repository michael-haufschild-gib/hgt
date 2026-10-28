# Literal physical normalization of dyadic details

Let U be the logarithmic-cell embedding, W_p its actual integer translation,
and d_a the unit balanced dyadic detail. Then

sqrt(haarMass a) * U(d_a) = haarAtom a.

The equality holds after every W_2 power and every W_p, p>=2, with the
corresponding literal half-line logarithmic translation on the physical side.
The complete physical cell also equals U(sqrt(ell_a)*e_a).

The proof uses the parent-width telescope ell_(2a)+ell_(2a+1)=ell_a and
positive square-root multiplication. Both coordinates match the existing
Haar coefficients, so no new source or form replaces the original one.

Lean: `SignedArithmeticHodgeTheory/TheDyadicDetailsAreTheLiteralBalancedHaarSources.lean`.
Capstones: `sqrt_haarMass_smul_logCellEmbedding_detail`,
`sqrt_haarMass_smul_logCellEmbedding_detail_pow`, and
`sqrt_haarMass_smul_logCellEmbedding_detail_shift`.
Individual final no-olean Lean audit passes; transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound` only.

This supplies exact normalization for physical Gamma estimates. It does not
bound the joint cost across levels or establish the complete Weil sign.
