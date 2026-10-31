# Prime conductor heads and tails have opposite torsion limits

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Q1/O1](three-frontier-questions-full-solutions.md).

For positive conductors `m,l`, set `delta=1_(m=l)`,
`d=sqrt(phi(m)phi(l))`, `v_m,N(n)=c_m(n)/sqrt(phi(m)n log N)`,
and `A_K=sum_(k<K)Lambda(k)/k`. Let `H_K,N(m,l)` be the literal
prime-matrix pairing restricted to dilation ratios `k<K`.
The proposed exact boundary laws are

`lim_K lim_N [H_K,N−2delta A_K]`
`=I(m,l)/d−delta[log m+tameDifferent(m)]`,

`lim_K lim_N [<v_m,N,P_N v_l,N>−H_K,N−delta(log N−2A_K)]`
`=−2I(m,l)/d`.

For distinct conductors no diagonal subtraction is needed. The fixed-dilation
head contributes the positive torsion edge; the complementary prime boundary
pays twice that edge. Both mixed orientations are retained.

## Reduction

For fixed `k`, logarithmic averaging through `N/k` retains the complete
period mean of `c_m(n)c_l(kn)`. Sum the existing completed upward-row
identity over one common period against `c_m`. Its correction is
`J_l−(log l+tameDifferent(l))c_l`. The divisor-jet expansion gives the
oriented mean `phi(m)Lambda(l/m)1_(m|l)−delta phi(m)tameDifferent(m)`.
Finite period sums commute with the convergent prime correction. Adding
the reverse orientation identifies the centered head limit. Subtract
from the full prime finite part to obtain the tail law.

Lean verification is pending. This is a signed prime boundary identity;
the Gamma, pole, and non-ratio successor boundary remain to be combined.
