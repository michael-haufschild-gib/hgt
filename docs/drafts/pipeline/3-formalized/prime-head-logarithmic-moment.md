# The logarithmic moment of a prime head

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Power-cutoff conductor heads](square-root-prime-heads-diagonalize-conductor-finite-parts.md).

The exact weighted Mertens asymptotic is

`[sum_(n≤N) Lambda(n)log(n)/n − (log N)²/2]/log N → 0`.

Write `e_N=sum_(n≤N)Lambda(n)/n−log N+gamma` and
`Delta_n=log(n+1)−log n`. Abel summation gives the exact identity

`sum_(n≤N)Lambda(n)log(n)/n−(log N)²/2`
`=log N e_N+(1/2)sum_(n<N)Delta_n²−sum_(n<N)e_n Delta_n`.

Mertens gives `e_N→0`. The squared increments have bounded sum;
harmonic weighted averaging makes the last sum `o(log N)`.

Lean: `SuccessorShellArithmetic/Conductor/PrimeConductorLogMoment.lean`,
`tendsto_primeHeadLogMoment_remainder`.
Final direct `lake --old env lean` check passed; transitive axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
