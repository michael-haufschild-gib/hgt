# The sign gauge sees successor pairs along Pell orbits

- **ID:** acg-sign-gauge-pell-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry README §9 topic 4
- **Statement:** The sign-gauge second moment of `C_h = Σ a_j a_{j+h}` is
  `2^{|S|} Σ_{j,j'} [j(j+h)·j'(j'+h) = □] a_j a_{j+h} a_{j'} a_{j'+h}` = phase-gauge variance + Pell
  part; every non-square `j(j+h)` lies in an infinite Pell class; the Pell part is unbounded.

## Proof
Sign orthogonality on `j(j+h)` (multiplicativity of sign twists). Pell: `X = 2j+h` solves
`X² − 4MU² = h²`, `M = j(j+h)`, `U = 1`; the unit `(2c+1) + b√(4M)` (`c²+c = Mb²`, from
`Pell.exists_of_not_isSquare`) maps solutions to strictly larger ones, `J' = (2c+1)J + ch + 2MbU`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheSignGaugeSeesSuccessorPairsAlongPellOrbits.lean`:
`sum_sq_signTwistedSuccCorr`, `sum_sq_signTwistedSuccCorr_eq`, `pell_step`, `exists_pell_unit`,
`exists_large_pellClass`, `exists_le_card_pellPairs`. Axioms standard.

## Insight
Sign (real) multiplicative data are strictly richer than phase data on successor correlations: the
mean sees finitely many square pairs, the second moment infinitely many Pell coincidences.
