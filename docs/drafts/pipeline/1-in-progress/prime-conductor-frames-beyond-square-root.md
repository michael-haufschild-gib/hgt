# Prime-conductor frames beyond the square-root horizon

- **Stage:** 1-in-progress; novelty and Lean checks pending.
- **Wall:** Σ1e.
- **Target:** For `1/2<θ<1`, prime conductor packets supported on `sqrt N<p≤N^θ` have a lower frame bound independent of `N`. No prime-distribution estimate is required.

## Disjoint-support mechanism

Write `H_k=Σ_(1≤n≤k)1/n`, `L=log N`, and `M=floor(sqrt N)`.
For a finite set of primes in that band, put
`s=Σ_p a_p/sqrt(p−1)` and
`A(n)=Σ_p p a_p 1_(p|n)/sqrt(p−1)`.
The Ramanujan identity `c_p(n)=p 1_(p|n)−1` gives packet coordinates
`(A(n)−s)/sqrt(nL)`.

Distinct prime divisibility supports are disjoint because `pq>N`.
They also vanish on `n≤M`. Weighted Cauchy–Schwarz therefore gives

`Σ_(n≤N)(A(n)−s)²/n ≥ (H_M/H_N) Σ_(n≤N)A(n)²/n`.

Disjointness evaluates the latter sum exactly:

`Σ_(n≤N)A(n)²/n = Σ_p [p/(p−1)] H_floor(N/p) a_p²`.

It also gives the full Gram identity. With
`T=Σ_p a_p H_floor(N/p)/sqrt(p−1)` and
`D=Σ_p [p/(p−1)] H_floor(N/p) a_p²`,

`L‖Σ_p a_p v_p‖² = D + H_N s² − 2sT`.

Thus the prime Gram is a positive diagonal plus a correction of rank at most two.
This identity only requires `pq>N` for distinct primes in the family.

Thus the proposed sharp finite lower bound is

`‖Σ_p a_p v_p‖² ≥ [H_M/(L H_N)] Σ_p [p/(p−1)] H_floor(N/p) a_p²`.

For `L≥1`, harmonic integral bounds give `H_M/H_N≥1/4` and
`H_floor(N/p)≥log(N/p)≥(1−θ)L`. Consequently

`‖Σ_p a_p v_p‖² ≥ (1−θ)/4 Σ_p a_p²`.

The square-root threshold helps this restricted family: it separates its
divisibility supports. This does not settle frames for all composite conductors,
nor their complete-Weil residual averages.

## Remaining proof work

Verify the exact Ramanujan normalization and harmonic-sum identities against the
corpus. Formalize the finite weighted projection bound, the disjoint-support
identity, and the polynomial-band lower bound. Audit the final theorem's axioms
before changing Σ1e's status.
