# The full logarithmic Mangoldt tail

- **ID:** RIAC-logarithmic-Mangoldt
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Full logarithmic torsion](../1-in-progress/riac-logarithmic-torsion-completion.md)
- **Lean:** [LogarithmicMangoldtTail.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/LogarithmicMangoldtTail.lean)

## Exact result

For every real `a>1`,

`Σ_(n≥1) Λ(n)/(n(1+log n)^a) < ∞`.

The proper-prime-power reciprocal Mangoldt series is also summable.

## Proof and prior work

On primes, the summand is bounded by `1/(p(log p)^(a−1))`.
The existing `RHTower.Sieve.summable_primes_one_div_mul_log_rpow` proves
summability for every `a−1>0`. On nonprimes, the logarithmic denominator
is at least one. The existing
`RHTower.sum_nonprime_vonMangoldt_rpow_le` bounds all finite positive
proper-prime-power sums at reciprocal weight by `72`. Enlarging arbitrary
finite supports to conductor intervals gives summability. The zero coordinate
contributes zero.

The contribution is the exact full Mangoldt tail needed by the forward
divisor row of logarithmic torsion. No new prime-density estimate is claimed.
The production file passed its direct Lean check and both transitive axiom
audits, using only `propext`, `Classical.choice`, `Quot.sound`.
