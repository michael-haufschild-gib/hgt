# Rank-controlled mean squares below smooth support length

- **ID:** CDG-SMOOTH-RANK
- **Stage:** 1-in-progress
- **Type:** CANDIDATE

## Target

For distinct primes `p₁,…,p_k≤y`, let
`A_H={∏p_j^e_j: 0≤e_j≤H}`. Below the rank-`r` depth floor `Δ`,
prove that each multiplicative window
`{m∈A_H: |log m−log n|<δ}` contains at most `(H+1)^(r−1)` points.
Gallagher's proved almost-diagonal estimate should then give

`∫_[−W,W] |Σ_(n∈A_H) a_n n^(2πit)|² dt`
`≤ 5/(4δ) · (H+1)^(r−1) Σ_(n∈A_H)|a_n|²`,

when `0<δ≤Δ(r,k−r,y,H)` and `2πδW≤1`.

## Mechanism and significance

Subtract the exponent vector of the window centre. All differences lie in
the proved near-relation span of dimension at most `r−1`. An injective
coordinate projection of that span is also injective on this affine fibre;
the original coordinates have `H+1` choices each.

For fixed primes, the rank floor is a power of `H`. Thus this controls
smooth polynomials at observation times polynomial in `H`, although their
integer support reaches exponential size in `H`. Penultimate rank should
save two powers of `H` against the trivial support-cardinality bound, using
only the two-logarithm Baker exponent. This is a short-time energy estimate,
not a constant-precision return exclusion.

## Dependencies and open work

`CollectiveRankDepth.nearRelationBox_finrank_le` supplies the arithmetic
rank bound. `GallagherAlmostDiagonal.integral_Icc_normSq_logPoly_le_count`
supplies the analytic transfer. The affine fibre count, its exact smooth
integer realization, and the polynomial observation scale remain to prove.
