# Power–logarithmic boundary of arithmetic torsion

- **ID:** RIAC-power-log-spectrum
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Logarithmic torsion](../1-in-progress/riac-logarithmic-torsion-completion.md)
- **Statement:** Classify boundedness, compactness and Hilbert–Schmidt membership on weights `w(n)=n^δ(1+log n)^α`, retaining the original arithmetic matrix.

## Proposed exact ranges

Boundedness and compactness should hold precisely when
`δ>0`, or `δ=0` and `α>2`.
Hilbert–Schmidt membership should hold precisely when
`δ>1/2`, or `δ=1/2` and `α>1/2`.

HHAC proves the pure-power Hilbert–Schmidt boundary `δ>1/2`.
The logarithmic endpoint `δ=0` is under separate verification. The new
question is the logarithmic refinement at `δ=1/2` and a faithful comparison
of the two-parameter carriers. No theorem asserting these full ranges is
formalized yet.

## Critical square-mass mechanism to prove

Write `L(n)=1+log n`. At `δ=1/2`, the divisor-pair square is

`m⁻¹ Λ(t)² t⁻³ᐟ² L(m)⁻α L(mt)⁻α`.

For positive `α`, this is bounded by the product of the critical conductor
series `Σ_m 1/(m L(m)^(2α))` and a convergent prime-ratio series.
The expected boundary is therefore `2α>1`.

The diagonal needs arithmetic information beyond `d(n)≤log n`.
Expand `d(n)=Σ_(p|n) a_p`, where `a_p=log p/(p−1)`. The required moment
bound reduces to finiteness of `Σ_(p,q) a_p a_q/lcm(p,q)`, separating
`p=q` from `p≠q`. Nonnegative reindexing should then control the same
critical conductor series. Even conductors, where `d(2n)≥log 2`, force
the converse boundary.

## Audit requirements

Construct the normalization and arithmetic pairing comparison explicitly.
Prove the diagonal moment estimate and all endpoint series, including
negative logarithmic exponents away from the boundary. Check transitive
axioms before accepting any range. Existing generic Hilbert–Schmidt and
weighted Mangoldt operators are prior work; no novelty claim is made.
