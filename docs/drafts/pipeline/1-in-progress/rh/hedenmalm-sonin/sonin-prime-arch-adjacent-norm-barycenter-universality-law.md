# Sonin prime--archimedean adjacent-norm barycenter universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- SoninPrimeArchAdjacentNormTomography: monomial norms recover even energy moments and adjacent
  binomial norms polarize the intervening odd moments; sequence convergence is equivalent to
  all-moment convergence.
- SoninPrimeArchMomentBarycenter: a positive aperture measure matching every energy moment transfers
  Sonin positivity to the prime--Gamma Hankel form and implies RH.

Whole-corpus search found no measure-level sparse-probe characterization of the moment barycenter.

## Universal law

A positive aperture measure is a complete Sonin/prime--Gamma moment barycenter if and only if its
integrals against the two probe families `X^n` and `X^n + X^(n+1)` equal the corresponding even and
adjacent prime--Gamma moment combinations for every `n`. The sparse condition still implies RH.

## Paper proof

Monomial identity gives even moments directly. Adjacent-binomial identity is
`A_n = m_(2n) + 2m_(2n+1) + m_(2n+2)`. Forward implication follows by linearity of the integral.
Conversely, subtract neighboring monomial identities from `A_n` and divide by two; this recovers
both integrability and integral value of every odd moment. Even and odd cases exhaust all orders.
No numerical computation is used.

## Lean formalization

Module:
GaloisForLFunctions.RHTower.SoninPrimeArchAdjacentNormBarycenterUniversalityLaw.

Exact command:
lake env lean GaloisForLFunctions/RHTower/SoninPrimeArchAdjacentNormBarycenterUniversalityLaw.lean.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
