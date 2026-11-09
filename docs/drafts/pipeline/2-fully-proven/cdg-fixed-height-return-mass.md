# Fixed-height prime return mass

- **ID:** CDG-MASS
- **Stage:** 2-fully-proven
- **Type:** CALIBRATION
- **Source:** Collective Diophantine Geometry, heavy-subset breadth question.

## Exact statement

Write `θ(x)=Σ_{p≤x}log p`. For `0<q<r<1`,

`Σ_{j≥0}(θ(xq^j)−θ(rxq^j))/x → (1−r)/(1−q)` as `x→∞`.

For `0<δ<1`, set `q=e^(−2π)`, `r=e^(−2δ)` and
`x_N=e^(2πN+δ)`. Let `P_N` be the union, for `0≤j≤N`, of the
primes in `(rx_Nq^j,x_Nq^j]`. Then every `p∈P_N` satisfies
`p≤x_N` and `|log p−2πm|≤δ` for some integer `m`, while

`Σ_{p∈P_N}log p / θ(x_N) → (1−e^(−2δ))/(1−e^(−2π))`.

Consequently every smaller required logarithmic mass fraction is attained
by returning subsets at height `1`, for arbitrarily large prime cutoffs.

## Paper proof

The unconditional prime number theorem gives `θ(cx)/x→c` for every
`c>0`. The global Chebyshev estimate gives `0≤θ(u)≤Cu` for `u≥0`.
Monotonicity therefore bounds each normalized window mass between zero and
`Cq^j`. This geometric majorant is summable. Dominated convergence for
series gives the first limit, since the sum of the termwise limits is
`Σ_j(1−r)q^j=(1−r)/(1−q)`.

If `j<k`, then `xq^k≤xq^(j+1)<rxq^j`; hence the windows are disjoint.
For `x=x_N`, their upper endpoints are `exp(2π(N−j)+δ)`. When `j>N`
these are less than `1`, so those windows contain no primes and both
Chebyshev terms vanish. Thus the infinite sum equals the logarithmic mass
of the finite union `P_N`. A member of its `j`th window satisfies
`2π(N−j)−δ<log p≤2π(N−j)+δ`, proving the phase condition.
Finally `x_N→∞` and `θ(x_N)/x_N→1`, giving the claimed relative mass.
Convergence above any smaller fraction and unboundedness of `x_N` give
the final existence statement.

## Scope and novelty

The positive survivor is an exact mass law for infinitely many cutoffs,
with actual returning prime subsets. It calibrates the admissible heaviness
parameter; it does not exclude near-full returns in the remaining range.

The underlying nonuniform logarithmic phase distribution is classical:
Wintner (1935), reviewed in Hutson, *On the distribution of log(p)* (2003),
Theorem 2.1, https://www.ijpam.eu/contents/2003-7-4/6/6.pdf.
No new prime-distribution estimate or breadth lower bound is claimed.

## Lean status

Paper proof dependency-closed. Formalization in progress.
