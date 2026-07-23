# Integral multiplicative periodic gear-count universality law

## Status

Formalized in Lean and wired into the RHTower umbrella. Kept in progress until global exhaustion
and final audit complete.

## Lean sources

- `GaloisForLFunctions.RHTower.UnboundedGearCount`
- `GaloisForLFunctions.RHTower.DichotomyInstances`
- `GaloisForLFunctions.RHTower.IntegralFEPolynomial`

## Conjecture

For every finite bound, one integral multiplicative degree-zero functional-equation carrier has
at least that many distinct real parts strictly between `0` and `1/2`, and through every selected
real part its zero set contains a full two-sided vertical arithmetic progression.

Thus integrality, multiplicativity, finite Dirichlet support, and the exact functional equation
do not merely permit unboundedly many off-line zero locations: they permit unboundedly many
distinct off-critical periodic zero combs in one carrier.

## Corpus gap

The gear-count theorem produces arbitrarily many distinct real off-line zeros. The periodicity
dichotomy theorem says every zero of every integral multiplicative FE carrier enters a full
vertical progression. No theorem applies the dichotomy simultaneously to the entire unbounded
gear set.

## Proof plan

1. Take the carrier and finite real zero set from the gear-count theorem.
2. Apply the class-wide periodicity dichotomy at each selected zero.
3. Exclude the critical-line branch using `σ < 1/2`.
4. Retain the progression period separately for every selected real part.

No numerical computation is used.

## Novelty status

Post-proof searches found general work on zeros and almost-periodicity of Dirichlet polynomials,
Dirichlet series satisfying Riemann-type functional equations, and nonvanishing of classical
`L`-functions on vertical arithmetic progressions. No searched source stated the exact unbounded
simultaneous zero-comb theorem for integral multiplicative finite-support coefficient streams
with the degree-zero functional equation. Novelty claim is restricted to that precise class and
construction.

## Lean result

`formal/GaloisForLFunctions/RHTower/IntegralMultiplicativePeriodicGearCountUniversalityLaw.lean`
proves that for every `n`, one member of `IntegralMultiplicativeFEClass` carries at least `n`
distinct real parts in `(0, 1/2)`, each supporting a full two-sided vertical arithmetic
progression of zeros.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/IntegralMultiplicativePeriodicGearCountUniversalityLaw.lean`
