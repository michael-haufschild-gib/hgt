# Integer rounding of a Beurling one-off

- **ID:** integer-rounding-preserves-beurling-one-off-divisor
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Replacing the discrete one-off prime norms `p_k` by `ceil(p_k)` preserves its finite nonempty zero layer on `Re s > 1/2`.

## Relevance to AAL

Test whether integer norms alone distinguish the actual zeta function from the existing one-off models. This does not decide AAL for the actual zeta function and makes no assertion about the rounded system's integer-count error or functional equation.

## Candidate mechanism

For logarithmic norms `t_k`, rounding gives `t_k ≤ u_k ≤ t_k + exp(-t_k)`. The difference of the prime sums should converge locally uniformly on `Re s > 0`, since its terms are bounded on compact sets by a constant times `exp(-(1 + Re s)t_k)`. The existing prime-power remainders are holomorphic on `Re s > 1/2`. Their difference and the prime-sum correction should give a holomorphic nonvanishing Euler quotient there.

## Gates

- [x] Existing discrete model and its exact zero set checked in source.
- [ ] Rounding bounds, locally uniform convergence and Euler-product identity formalized.
- [ ] Integer-norm one-off instantiated and transitive dependencies audited.
- [ ] Consequences for the actual AAL research recorded without claiming a decision.
