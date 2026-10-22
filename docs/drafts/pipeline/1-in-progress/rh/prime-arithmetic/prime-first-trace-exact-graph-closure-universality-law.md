# Prime first-trace exact graph-closure universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `RHTower/ArithmeticLogClockFiniteJetSaturation.lean`
  - `hardyPrependZero_comp_primeFiniteTraceClock_one`
  - `hardyDrop`
- `RHTower/ArithmeticLogClockBoundedCompletionSaturation.lean`
  - `primeBoundedPostprocessedTraceClock_pair_mem_graphClosure`
- `RHTower/ArithmeticSchurFirstTraceNonclosability.lean`
  - `primeFirstTraceClock`
  - `primeHardyKernelMap`

## Universal law

The graph closure of the actual-prime first-trace clock is exactly the codimension-one product
sector consisting of every Hardy source paired with every Hardy response whose vacuum coordinate
is zero.  Equivalently,

`(x,y) ∈ closure Graph(kernelMap, firstTraceClock) ↔ y(0)=0`.

This sharpens a single graph-null nonclosability witness to a complete classification of all
possible closed-graph limits.

## Paper proof

Zero-prepending preserves the full `ℓ²` norm and has range exactly the zero-vacuum sector, with
`hardyDrop` as inverse on that sector.  The order-one finite trace clock followed by zero-prepending
is exactly the first-trace clock.  Bounded-completion saturation therefore places every pair
`(x, prepend(y))` in the first-trace graph closure, proving the reverse inclusion.  For the forward
inclusion, every actual first-trace response has zero vacuum coordinate and that coordinate kernel
is closed, so the entire graph closure remains inside it.

## Lean status

Source complete in
`formal/GaloisForLFunctions/RHTower/PrimeFirstTraceExactGraphClosureUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceExactGraphClosureUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
finite-trace saturation, bounded postprocessing, and the order-one first-trace connector, but no
exact characterization of the first-trace graph closure as the zero-vacuum response sector.
