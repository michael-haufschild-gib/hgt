# Small-prime flips lie below the maximal gap

- **ID:** ACP-SMALL-PRIME-GAP-BOUNDARY
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** arithmetic-counting-positivity.md
- **Statement:** For a prime `p`, every hyperplane gap of the single-prime flip is at most `p log(p)/(p+3)`; this is below `2 log 2` for `p=2,3,5,7`.

## Purpose and ownership

This would settle the small-prime side left open by the independent
valuation-box theorem for primes at least 11. It uses the retained harmonic
spectral bridge for a new upper bound. It does not resume the discarded
prime-41 lower-bound endpoint or replace the other researcher's proof.

## Candidate arithmetic witness

Write `u_1,N` and `u_p,N` for the harmonically normalized Ramanujan modes,
and `v_p,N` for the unit prime-parity constraint. Let

`a_N=<v_p,N,u_p,N>`, `b_N=<v_p,N,u_1,N>`,
`z_N=a_N u_1,N-b_N u_p,N`.

Then `<v_p,N,z_N>=0` exactly at each horizon. The proved count gives
`b_N -> c_p` and `a_N -> -2c_p/sqrt(p-1)`, with
`c_p=(p-1)/(p+1)>0`. The Gram limit makes the two modes orthonormal in the
limit; their actual matrix residuals tend to zero. Their renormalized
energies are `gamma` and `gamma+p log(p)/(p-1)`.

The predicted limiting Rayleigh excess above `gamma` is therefore

`[c_p^2 * p log(p)/(p-1)] / [4c_p^2/(p-1)+c_p^2]
 = p log(p)/(p+3)`.

Multiplying `z_N` by the sign gauge gives an exactly harmonic-orthogonal
test for `HasHyperplaneGap`. This avoids correcting an asymptotically
orthogonal vector in a matrix whose norm grows with the horizon.

## Remaining paper obligations

Inspect the actual matrix/form identification, the finite-mode Gram limit,
and the finite-packet energy laws. Prove the varying-coefficient energy
limit and nonzero limiting mass before claiming the bound. The numerical
separation at prime seven can be proved by the exact integer inequality
`7^7<2^20`, logarithmic monotonicity, and monotonicity of `p/(p+3)` and
`log p` for `1<=p<=7`. No numerical experiment is needed.

## Novelty search

Corpus search for prime-parity upper gaps and small primes found the
single-prime lower bounds and the large-prime maximal-gap branch, but no
small-prime upper bound. Relevant Gram input surfaced as
`tendsto_ramanujanPoleProfile_gram` and `ramanujanHorizonVector_inner`.

## Gates

- [x] Exact candidate and arithmetic witness; initial corpus search.
- [ ] Inspect all inputs and close the paper proof.
- [ ] Lean formalization and transitive axiom audit.
- [ ] Canonical source check, umbrella, README, scratch cleanup.

The finite-prime density and exhaustion leaves are being completed first.
This card is not a proved result and makes no optimal-gap claim at small primes.
