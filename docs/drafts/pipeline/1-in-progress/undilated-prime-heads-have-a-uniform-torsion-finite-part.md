# Undilated prime heads have a uniform torsion finite part

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Q1/O1](three-frontier-questions-full-solutions.md);
  [Gram plateau](harmonic-gram-remainders-have-a-logarithmic-plateau.md).

For a real conductor packet through `Q`, write `M=sum a_m²`,
`G(Y)=sum_(n≤Y)(sum_m a_m u_m(n))²/n`, and let `T` be its normalized
torsion pairing. Put `A(N)=sum_(k≤N)Lambda(k)/k`. Conjecture one absolute
`C>0` such that, for all `Q,N≥2`,

`|2 sum_(k≤N)Lambda(k)G(floor(N/k))/(k log N)`
`−[2 sum_(n≤N)log(n)/n]/log N · M + 2A(N)T/log N|`
`≤C(1+log Q)² M/log N`.

The scalar term is exact: divisor summation gives
`sum_(k≤N)Lambda(k)H_(floor(N/k))/k=sum_(n≤N)log(n)/n`.

## Proposed proof

Write `R(Y)=G(Y)−H_Y M+T` and split at `K=floor(N/Q²)`.
For `k≤K`, the quadratic remainder gives
`|R(floor(N/k))|≤Q²kM/N`; Chebyshev summation costs at most `7M`.
For `k>K`, use the logarithmic plateau. Boundedness of the Mertens error
and logarithmic roundoff give
`A(N)−A(K)≤2log Q+O(1)`, also when `K=0`.
The weighted remainder is therefore `O((1+log Q)² M)` uniformly in both
cutoffs. Divide by `log N`.

This controls the full undilated component on growing packets. The actual
dilated correction, Gamma, pole, and successor-shell comparison remain
separate. Lean verification pending.
