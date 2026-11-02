# Exact cone cancellation with polynomial boundary approach

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** SC2; sharpness of polynomial boundary repulsion.
- **Target:** Strengthen the bounded-local-density exact-spline cone model so,
  for some `α,c,C>0`, every positive-quadrant atom satisfies
  `c(1+Im z)^(-α)≤D−Re z≤C(1+Im z)^(-α)`.

Retain exact coefficients `(sinh z/z)^8`, unit multiplicities, distinct
quartets, uniformly bounded unit-interval counts, summable coefficient norms,
vanishing positive two-prime cone moments, and bounded quartet coupling.
This would show polynomial boundary approach is compatible with these generic
zero-side conditions. It would not be a counterexample involving actual zeta zeros.

## Candidate proof

`exists_two_prime_sparse_spline_geometric_corrections` supplies node count,
span, height threshold, and inverse target radius bounded by `U R^k`.
Choose geometric heights `H_k=V S^k`, with `S>R` sufficiently large.
Then block coefficient norm is at most `B U R^k/H_k^8`, and the available
correction radius is at least `1/(U R^k H_k^8)`. The former is summable;
the latter decays geometrically. A late tail gives the required mass bounds,
height thresholds, cumulative-count bounds, and gaps between blocks.

Keep levels `δ_k=D−(D−d)2^(-k)` and cone cutoffs of order `8^k`.
The normalized residual at a new frequency is at most `2 exp(−c4^k)`,
which is eventually smaller than the geometric correction radius.
Exact prefix cancellation should therefore work at geometric heights.
Since `H_k≤Im z≤2H_k`, the width gap is comparable to
`(Im z)^(-α)`, with `α=log 2/log S`.

## Audits still required

The finite interpolation and geometric cost theorems are formalized.
The existing infinite schedule fixes heights through masses `exp(−4^k)`;
it does not prove this stronger claim. A general schedule with direct block
norm bounds, the geometric-height construction, and the polynomial comparison
remain unformalized. Complete the current bounded-local-density model first.

Local corpus search found the exact-spline model and its finite correction
lemmas, but no model with a two-sided polynomial width gap. External priority
has not been checked.
