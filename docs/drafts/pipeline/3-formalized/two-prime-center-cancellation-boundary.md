# Two-prime common-center cancellation boundary

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6

Write `W_a(s)=w_a(max(0,s))` and
`D_(p,h)f(s)=f(s)−2p f(s−h)+p²f(s−2h)`.
For `a≥0`, `0≤h≤k`, and `p,q≥0`,

`D_(p,h)D_(q,k)W_a(h+k)`
`=w_a(h+k)−2p w_a(k)−2q w_a(h)+p²w_a(k−h)`.

This is the exact minimum, over the two independent phase cosines, of
the squarefree two-generator common-center polynomial at `h+k`.
Before the second generator enters (`0≤s≤k`), the double difference is
nonnegative whenever `0≤p≤1`: all shifted terms involving `k` vanish,
leaving the proved one-prime convex payment.

For `h=log 2`, `k=log 3`, `p=1/√2`, `q=1/√3`, there exists
`0<ε≤1/2` such that this boundary value is negative for every `0<a<ε`.
Thus the nonnegative one-prime payment cannot be iterated pointwise.

## Proof of strict failure

The boundary value is

`V(a)=w_a(log 6)−√2 w_a(log 3)−(2/√3)w_a(log 2)+(1/2)w_a(log(3/2))`.

It vanishes at `a=0`, with derivative twice

`S=(2−√2−2/√3)log 2+(3/2−√2)log(3/2)`.

The elementary bounds `√2≥7/5`, `2/√3≥8/7`, `log 2≥1/2`, and
`0≤log(3/2)≤1/2` give
`S≤−19/70+1/20<0`. Differentiability forces `V(a)<0` just to the
right of zero. Expansion of the two finite differences proves the exact
boundary identity; nonnegative cosine increments prove the minimum law.

This is a common-center obstruction before radial integration. It does
not give a negative integrated aperture spectrum. The
[complete geometric-chain spectrum](geometric-theta-aperture-spectrum.md)
remains strictly positive.

## Lean

`CompletedArithmeticForms/TwoPrimeApertureCenter.lean` proves
`aperturePrimeDifference_two_nonneg_before_second`,
`aperturePrimeDifference_two_boundary`,
`twoPrimeCenter_boundary_minimum`, `aperturePrimeDifference_two_log6`,
and `aperturePrimeDifference_two_eventually_neg`.
Direct source check passed; five capstone dependency audits contain only
`propext`, `Classical.choice`, `Quot.sound`.
