# Finite-prime aperture census universality law

## Status

Law 249; paper proof and exact Lean module audit passed. Literature novelty audit pending.

## Corpus sources

- `RHTower/ThetaCusp/ThetaCuspMellinPole.lean`
- `RHTower/PrimeLogExponentialTypeUniqueness.lean`
- `RHTower/GaussPairedChannelSchattenCapstone.lean`
- `RHTower/GaussPairedChannelSchattenDepth.lean`

## Theorem-first derivation

Four terminal mechanisms expose the same finite-aperture integer `π(N)`: exact theta-cusp order,
minimum divisor mass of an entire prime-log vanishing carrier, half the exact Gauss-paired Schatten
threshold, and rank of the finite prime-state module. No existing theorem identifies these as one
shared census.

## Universal law

At every nonempty finite prime aperture, one integer controls four different geometries:

1. the cusp denominator vanishes to order `π(N)` and its inverse has pole order `-π(N)`;
2. every nonzero entire carrier vanishing at all prime logarithms has divisor mass at least `π(N)`
   in the canonical radius-`log N` ball;
3. a certified `π(N)`-channel Gauss system has exact Schatten transition at `2π(N)`;
4. a prime-state space of rank `π(N)` obeys the same coefficient/complement capacity budget.

## Paper proof

Apply the four source theorems at the same `N`. Rewrite `gaussPairedCriticalDepth N` by its
definition `2 * π(N)` and rewrite the prime-state rank hypothesis by the exact arithmetic
intersection/complement split. Every displayed equality or inequality then has the same middle
integer `π(N)`.

No numerical pre-certification applies: theorem is an exact identification of already formalized
orders, ranks, and thresholds.

## Lean target

- Module: `GaloisForLFunctions.RHTower.FinitePrimeApertureCensusUniversalityLaw`
- Capstone: `RHTower.finitePrimeAperture_cuspDivisorSchattenRankUniversality`
- Exact check: `lake env lean GaloisForLFunctions/RHTower/FinitePrimeApertureCensusUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
