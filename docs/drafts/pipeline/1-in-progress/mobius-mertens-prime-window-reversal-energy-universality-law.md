# Möbius–Mertens prime-window reversal-energy universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- `mobiusMertensPartialSum_eq_primeWindow`: every Mertens partial sum is exactly one prime-free
  interval-window sum for any selected prime.
- `mobiusMertensSelfConvolution_re_eq_palindromic_sub_antipalindromic`: reversal polarization
  decomposes self-convolution into positive palindromic and antipalindromic energies.
- `mobiusMertensPalindromicEnergySubpowerUpperBound_implies_riemannHypothesis`: subpower control of
  positive palindromic energy implies RH.

Corpus research found no theorem transporting reversal energy or its RH criterion through the
arbitrary one-prime window representation.

## Universal law

For every pair of primes `p,q` and every cutoff `N`, palindromic reversal energies computed from
the `p`-free and `q`-free windows agree exactly. For any single chosen prime, window-energy
subpower criterion is equivalent to global Mertens palindromic-energy criterion and therefore
implies RH.

## Paper proof

Substitute exact prime-window formula for both Mertens partial sums in every antidiagonal summand
of palindromic energy. This proves energy identity termwise for each prime. Transporting pointwise
identity through quantified subpower bound gives criterion equivalence. Existing positive-energy
consumer gives RH implication. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.MobiusMertensPrimeWindowReversalEnergyUniversalityLaw`.

Exact command:
`lake env lean GaloisForLFunctions/RHTower/MobiusMertensPrimeWindowReversalEnergyUniversalityLaw.lean`.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
