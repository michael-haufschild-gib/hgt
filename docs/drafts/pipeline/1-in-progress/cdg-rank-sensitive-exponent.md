# A uniform rank-sensitive exponent and approximation rank profile

- **ID:** CDG-EXP
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Goal:** Convert the explicit simultaneous logarithm bound into a simple
  dimension-and-rank estimate and a uniform threshold for all near relations.

## Target

For `k=d+r`, `r≥1`, `W≥1`, let `P` be the explicit collective parameters,
`h=floor(d/r)+1`, and `U=10⁴(W+1)(k+1)²`. Prove

`collectiveLambdaExponent(P)+1 ≤ U^(100h(k+1))`.

Since `h=floor(k/r)`, this retains the reciprocal-rank gain in the exponent.
Use a parameter choice depending only on `(k,r,W)`, then show that integer
vectors of height at most `H` with scalar product below the resulting
rank-`r` floor span at most `r−1` rational dimensions. Keep the existing
full-rank determinant and scalar reduction bounds as additional floors.

## Estimates to verify

With `B=1000Wk` and the explicit `L,J,R` from CDG-SIM,

`2^R ≤ 4(2B)^(h(k+1))(2(L+J+1))^(2J)`.

The binary-logarithmic expression permits polynomial bounds for `R`
separately from this exponential bound. In particular, coarse bounds
`R+1≤U⁶`, `E≤U⁷`, `q≤U^(13h)`, and
`2^R≤U^(19h(k+1))` suffice to control every term of the exact coefficient.
The existing `lambda_polynomial_le` bounds the coefficient polynomial by
`200Zv³` when every parameter is at most `v` and `2^R≤Z`. With
`v=U^(30h)` and `Z=U^(19h(k+1))`, this fits the target exponent.
These coarse inequalities and the proposed exponent are not yet formalized.

## Boundary

A stronger approximation rank profile is not a return-counting theorem.
Constant phase precision still limits the coefficient heights that can act
on a return. The breadth mechanism remains open.
