# Prime-block feedback and multiscale cancellation

- **ID:** PRIME-BLOCK-FEEDBACK
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; tested feedback and contraction proposals fail numerical discrimination
- **Source:** `PrimeLogBlockCompression`; literal ordinary primes
- **RH chain:** retained prime counts and log sums -> uniform signed source estimate (open) -> right-half-strip zero exclusion (open) -> RH

## Current mathematical state

Quartic source compression is closed in Lean, including the complete arithmetic error and nonzero quotient limit. It does not bound the retained counts or logarithmic means. The computations in [the report](../2-fully-proven/computations/prime-block-feedback-2026-09-06/REPORT.md) discriminate three prospective cancellation mechanisms; none supplies the missing estimate.

Eight-lag count/centroid prediction fails its frozen discovery gate. Uniform 20% reduction at every dyadic merge also fails discovery. Average reduction from sixteen fine cells to a full block survives all eight prescribed boundary shifts on both held-out ranges, but pointwise reduction does not: 43 of 448 later phase/block observations expand. The largest audited ratio is 3.7701766672255 at `k=76`, shift `5/8`. These are numerical results, not Lean theorems or a proof that an arithmetic route cannot close.

The fixed average ceiling `1/2` also fails its larger-scale persistence test. It holds on all phases in `k=128..159`, but the unshifted ratio is `0.50882142` on the doubled proportional band `k=256..319`. The other seven phases pass. The threshold is not changed; this does not exclude other scale-dependent estimates.

## Failed conjecture and positive-salvage audit

For each sixteen-cell group, `L_j=integral dx/log x` and `C_j=prime_count-L_j`. The independently frozen pointwise conjecture was

`(sum C_j)^2/(sum L_j) <= (1/16) sum C_j^2/L_j`.

Its numerical counterexample has a positive gap 0.70170664286144, fresh interval-sieve agreement, and independent 60-/90-digit integral checks. The stronger inequality cannot be inferred from the surviving mean-square suppression.

The second pass tested all prescribed boundary shifts without selecting favorable ones; its aggregate endpoint bridge survives only on the initial finite ranges and fails its last scale extension. No paper proof extending it is closed. Cross-term expansion is already generic corpus algebra. **NO POSITIVE SALVAGE FOUND at the level of a new dependency-closed theorem.** Formalization is not claimed, and the source route remains open.

## Remaining independent producer

A successful source estimate must handle locally amplifying clusters and their accumulated signed contribution, including the relevant Mellin phases. Neither an average over sampled blocks, an eight-step recurrence, nor monotone contraction at each merge has supplied this. The present experiment supports no all-scale replacement conjecture. Repeating favorable averages or enlarging a fit without an arithmetic mechanism is not the next proof step.
