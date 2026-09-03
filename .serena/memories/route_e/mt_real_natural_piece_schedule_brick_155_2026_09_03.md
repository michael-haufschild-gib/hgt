# Route E / Matomäki–Teräväinen Brick 155 (2026-09-03)

Added `formal/GaloisForLFunctions/RHTower/Sieve/MatomakiTeravainenRealNaturalPieceSchedule.lean`.

Key correction: the upper-adic index in retained Proposition-2.2 boxes can be zero, so a natural
window theorem for every `mtUpperAdicScale delta k` is false.  Use the retained product lower
bound instead.

New declarations:

- `eventually_two_rpow_le_mtPaperWidth_mul_rpow`
- `mtUnitFloor_conditions_of_half_width`
- `eventually_mtPaperTypeIPiece_unit_eq_wattBlock`
- `MTTypeI_II_PieceData.first_two_product_le_rpow_five_eighth`
- `eventually_mtPaperTypeI_II_Piece_unit_eq_wattBlock`

For literal paper-range Type-I data, `M1 <= X^(1/2+epsilon)` and `Y/2 < M1*M2` force
`mtPaperWidth (A+1) X * M2 >= 1`.  For Type-I/II data, squaring gives
`M1*M2 <= X^(5/8)`, then `Y/2 < M1*M2*M3` forces the same result for `M3`.  Both real unit
factors are therefore exact nonempty dyadic natural Watt blocks eventually, with no adic-index
premise.

Verification:

- direct `lake env lean` source check passed;
- targeted leaf build passed `11141/11141`;
- all five new declarations have axioms `[propext, Classical.choice, Quot.sound]` only;
- imported by `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.

Remaining core: route all full Proposition-2.2 pieces through receivers and close the genuinely
collective signed cross-modulus / Deshouillers–Iwaniec-strength residual Type-I range before the
Perron comparison and all-interval E3 theorem.
