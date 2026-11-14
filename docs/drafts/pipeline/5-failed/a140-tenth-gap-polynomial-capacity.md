# The tenth-gap polynomial capacity has a negative second minor

- **ID:** A140-tenth-gap-capacity
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/a140-certificates-through-the-prime-five-boundary.md`.
- **Rejected statement:** The first two principal minors of the specified
  charge-adjusted polynomial capacity matrix are positive.

## Exact obstruction

Put `b=523719/2000000`, `w=49013/100000`, `a=5493/10000`,
`H=7381/2520`, `c=507/5000`, and `δ=1/100000`. Define

`q(x)=100/111−2029x²/5000−201x⁴/10000−87x⁶/2500−203x⁸/10000−17x¹⁶/200`.

Let `P₀=1`, `P₂=(3x²−1)/2`, `h=(1−b)/2`,
`x(t)=(1+b)/2+ht`, `y(t)=(1+b)/2−ht`, and
`z(t)=w²q(x(t))q(y(t))`, `g(t)=1+z(t)+z(t)²+15z(t)³/13`.
For `i,j∈{0,2}`, set

`Cᵢⱼ=∫₀ᵇqPᵢPⱼ+h∫₀¹g[q(x)Pᵢ(x)Pⱼ(x)+q(y)Pᵢ(y)Pⱼ(y)`
`+wq(x)q(y)(Pᵢ(x)Pⱼ(y)+Pᵢ(y)Pⱼ(x))]dt`.

The charges are

`Q₀=H−7a/2−(1/36+c/24)a²−3a³/8−a⁵/198−a⁷/5760−a⁹/921600`,

`Q₂=5(H−3/2)+(5/252−5c/24)a²−5a⁵/396−a⁷/1008−a⁹/112896`,

`k=a²/72+3a³/8+25a⁵/2772+17a⁷/40320+a⁹/322560`.

With `D=Q₀Q₂−k²`, define
`B₀₀=Q₂−D(C₀₀+δ)`, `B₀₂=k−DC₀₂`, and `B₂₂=Q₀−D(C₂₂+δ)`.
Then **`B₀₀>0` and `B₀₀B₂₂−B₀₂²<0`**. Expanding the polynomials and
integrating each monomial reduces these inequalities to exact rational
inequalities. Thus this matrix cannot certify a positive floor.

## Positive survivor

Let `V(x)=111/100+Σ_{j=1}^{32}x^{2j}/(2j)`. On `[0,1]`, `q>0` and
`Vq≥1`. On `[0,1)`, `V≤111/100−log(1−x²)/2`, so `q` majorizes the
reciprocal logarithmic potential. For `x,y∈[0,1]` with
`63/50≤x+y≤127/100`, `q(x)q(y)≤11/20`.

For `z=x²`, homogenizing `Vq−1` on the five intervals with endpoints
`0,1/4,1/2,3/4,7/8,1` gives nonnegative coefficients. The finite logarithmic
sum lies below the logarithm. The pair bound follows from
`q(x)≤100/111−2029x²/5000`, together with
`x²+y²≥(x+y)²/2` and `xy≤(x+y)²/4`.

The obstruction is therefore at the matrix-capacity stage, despite valid
pointwise reciprocal and pair bounds. It does not establish a negative
direction for the actual Weil form.

## Lean

Module: `WindowTowerOfSpecZ/TheTenthGapReciprocalHasANegativeCapacityMinor.lean`.

- `primeThreeTenEvenReciprocal_bound`
- `primeThreeTenEvenPotential_le_log`
- `primeThreeTenEvenReciprocal_pair_bound`
- `TenthGapCapacity.inverse_pair_ratio_upper`
- `TenthGapCapacity.first_capacity_minor`
- `TenthGapCapacity.second_capacity_minor_neg`

The negative statement and positive survivor passed the direct
`lake --old env lean` check. All six transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import is present.
