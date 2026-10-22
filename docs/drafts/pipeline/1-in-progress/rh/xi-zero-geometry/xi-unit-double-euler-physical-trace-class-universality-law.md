# Xi unit-double Euler/physical trace-class universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- physicalPrimeEndpointWeight_eq_neg_fusedResponse_add_remainder: physical endpoint is negative
  fused current plus inverse-square correction.
- physicalEndpoint_add_unitDoubleFusedResponse_sum_eq_remainder: cancellation is support-blind in
  arbitrary real modules.
- xiUnitDoubleEulerResponseSpectralCoefficient_eq: unit-double Euler coefficient has exact
  von-Mangoldt rational form.
- xiUnitDoubleEulerResponseSpectralCoefficient_nonpos: every genuine Euler mode is nonpositive.

Whole-corpus research found no theorem joining physical endpoint and unit-double Euler spectral
coefficient at prime modes.

## Universal law

At every prime p, physical endpoint weight plus unit-double Euler spectral coefficient equals
2 log(p) / p². This remainder is strictly positive and summable over all primes. For every finite
prime set and arbitrary prime-labelled vectors in any real module, same cancellation holds
termwise.

## Paper proof

At a prime, von Mangoldt value is log(p). Add log(p)/p to
log(p)(2/p² - 1/p); non-summable 1/p terms cancel, leaving 2 log(p)/p². Positivity follows from
p > 1. Absolute summability follows from logarithmically weighted zeta convergence at exponent
two. Vector law follows by distributivity of scalar multiplication. No numerical computation is
used.

## Lean formalization

Module:
GaloisForLFunctions.RHTower.XiUnitDoubleEulerPhysicalTraceClassUniversalityLaw.

Exact command:
lake env lean GaloisForLFunctions/RHTower/XiUnitDoubleEulerPhysicalTraceClassUniversalityLaw.lean.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
