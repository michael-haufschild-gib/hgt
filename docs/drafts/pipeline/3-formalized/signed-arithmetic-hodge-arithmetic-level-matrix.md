# Arithmetic translation in complete dyadic coordinates

For the actual logarithmic-cell isometries, W_p W_2^j=W_2^j W_p, p>=2.
For u in the wandering space and arbitrary v,

inner(W_2^j u,W_p W_2^k v) =
if k<=j then inner(W_2^(j-k) u,W_p v) else 0.

Thus the complete coordinate matrix is triangular and constant along each
level diagonal. Its entries are read from the original arithmetic maps.
Prime two acts as an exact unilateral shift on every generator chain: its
zeroth coordinate vanishes and each successor coordinate is the preceding
coordinate of the source.

The proof commutes the actual multiplicative shifts, cancels common isometric
powers, and uses wandering orthogonality for the remaining strict inequality.

Lean: `SignedArithmeticHodgeTheory/ArithmeticTranslationsHaveAnExactDyadicLevelMatrix.lean`.
Capstones: `inner_logCellShift_dyadic_levels`,
`logCellArithmetic_level_matrix`, `logCellDyadicCoordinates_shift_zero`,
and `logCellDyadicCoordinates_shift_succ`.
Final individual no-olean audit passes; transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound` only.

This is an exact source representation. Joint Gamma payment, the complete
Weil matrix, pole constraints and the selective sign remain distinct tasks.
