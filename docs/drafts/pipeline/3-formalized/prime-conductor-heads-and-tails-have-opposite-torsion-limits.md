# Prime conductor heads and tails have opposite torsion limits

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md).

For positive conductors `m,l`, put `delta=1_(m=l)`,
`d=sqrt(phi(m)phi(l))`, `v_m,N(n)=c_m(n)/sqrt(phi(m)n log N)`,
and `A_K=sum_(k<K)Lambda(k)/k`. Let `H_K,N(m,l)` be the literal
prime-matrix pairing restricted to dilation ratios `k<K`. Then

`lim_K lim_N [H_K,N−2delta A_K]`
`=I(m,l)/d−delta[log m+tameDifferent(m)]`,

`lim_K lim_N [<v_m,N,P_N v_l,N>−H_K,N−delta(log N−2A_K)]`
`=−2I(m,l)/d`.

Both mixed orientations and the exact base cutoff `n≤N/k` are retained.
At `K=N+1`, the head equals the full prime matrix exactly.

## Proof

For fixed `k`, harmonic averaging through `N/k` retains the complete-period
mean of `c_m(n)c_l(kn)`. Sum the completed upward-row identity over a common
period against `c_m`. Its correction is
`J_l−(log l+tameDifferent(l))c_l`. The divisor-jet expansion gives the
oriented mean `phi(m)Lambda(l/m)1_(m|l)−delta phi(m)tameDifferent(m)`.
Finite period sums commute with the convergent prime correction. Adding
the reverse orientation gives the centered head limit. Subtracting it
from the full prime finite part gives the complementary boundary.

## Lean

`SuccessorShellArithmetic/Conductor/PrimeConductorHeadBoundary.lean`:

- `tendsto_primeConductorHeadMean_finitePart`;
- `primeConductorHeadPairing_horizon`;
- `tendsto_primeConductorHarmonicDilationMean`;
- `tendsto_primeConductorHeadPairing`;
- `tendsto_primeConductorHeadMean_sub_scalar`;
- `tendsto_primeConductorBoundaryPairing`;
- `tendsto_primeConductorBoundaryFinitePart`.

Final direct `lake --old env lean` check passed. All seven capstones depend
only on `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
The Gamma, pole, and non-ratio successor boundary remain to be combined.
