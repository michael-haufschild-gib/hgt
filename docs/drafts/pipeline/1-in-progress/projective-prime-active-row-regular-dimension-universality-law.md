# Projective-prime active-row regular-dimension universality law

## Status

In progress — paper proof and Lean formalization complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/PrimeLocalizedRowRegularity.lean`
  - `primeLocalized_finMvPolynomial_mem_nonZeroDivisors_of_coeff_not_mem`
- `HTGeometry/ProjectivePrimeLocalIncidenceDimension.lean`
  - `localizedUniversalRowPolynomial_coeff`
  - `projectivePrime_activeBlockRing_krullDim`

## Universal law

Every projectively active row equation is coefficientwise prime localization of a global universal
row polynomial. A surviving coefficient makes each localized row individually a non-zero-divisor.
Simultaneously at least `card row - q` rows remain active, and their fresh-block incidence ring loses
one Krull dimension per active row in the established upper bound.

## Lean status

Formalized in
`formal/GaloisForLFunctions/HTGeometry/ProjectivePrimeActiveRowRegularDimensionUniversalityLaw.lean`.

Exact check:

```text
lake env lean GaloisForLFunctions/HTGeometry/ProjectivePrimeActiveRowRegularDimensionUniversalityLaw.lean
```

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
