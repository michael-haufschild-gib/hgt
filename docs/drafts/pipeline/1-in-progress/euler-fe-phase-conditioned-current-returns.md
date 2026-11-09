# Prime-phase returns of the continued rough current

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Euler–FE transport and exact-event theory.

## Target

Under `¬AAL`, one regular high line `1/2<σ<Re ρ<1` should satisfy:
for every cutoff `Y`, finite `P⊆primesBelow Y`, prescribed unit phases `α_p`,
and `η,δ>0`, there are arbitrarily large heights `t` with

`|p^(it)−α_p|<η` for every `p∈P`, and

`|ζ′/ζ(σ+it)+Σ_{p<Y}log p/(p^(σ+it)−1)|² < A_Y(σ)+δ`.

Here `A_Y(σ)` is the complete rough von Mangoldt square mass, tending to zero
as `Y→∞`. No tail truncation or phase-return premise is allowed.

## Mechanism to formalize

Use the smooth box probe

`R_k(t)=Π_{p∈P}Σ_{j=0}^k α_p^(−j)p^(ijt)`.

Unique factorization gives mean square `(k+1)^|P|`. Multiplication by
`p^(it)−α_p` telescopes one factor, so the normalized weighted mean of its
squared modulus is `2/(k+1)`. The continued-current conditioned mean gives
normalized rough energy exactly `A_Y(σ)` for each fixed probe.

Apply these means to the nonnegative cost consisting of rough energy plus
`λΣ_{p∈P}|p^(it)−α_p|²`. Choose `λ=(A_Y+δ)/η²`, then `k` so that the total
phase contribution is less than `δ`. A weighted-integral contradiction
produces a good point in every sufficiently high dyadic window.

The small-prime head includes primes outside `P`; their phases remain free.
Even controlling every prime below `Y` does not approximate a fixed low
continued profile: that finite Euler head itself changes with `Y`.
Thus the target supplies joint arithmetic returns, not exact zero transport.

## Dependencies and gap

The full conditioned current mean is formalized in
`../3-formalized/euler-fe-continued-conditioned-rough-mean.md`, including
the regular high line needed for integration. Box-probe coefficients,
their exact phase-error energies, and the point-selection argument still
require Lean proofs. Existing finite-tail moment theorems alone do not
discharge this infinite-current target.
