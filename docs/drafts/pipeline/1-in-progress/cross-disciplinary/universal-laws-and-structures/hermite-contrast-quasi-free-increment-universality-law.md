# Hermite contrast/quasi-free increment universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- HermiteContrastLp: exact squared norm of canonical constrained-prolate contrast.
- ConstrainedProlateHermiteContrast: secular coordinate `theta_k = Q_k / Q_(k+1)` and exact
  accumulated-mass recursion.
- HermiteEvenSlaterPluckerConnector: constrained-prolate weights as quasi-free Hermite occupations,
  with exact independent-mode mean, variance, and Fano formulas.

Whole-corpus search found no theorem relating contrast/secular energy to rank increments of the
quasi-free Slater--Pluecker observables.

## Universal law

Let `E_k` be normalized squared contrast energy, `Q_(k+1)` accumulated mass, and
`d_(k+1) = 4(k+1)`. Then next occupation is `Q_(k+1)(1-E_k)`. Therefore rank extension from
`k+1` to `k+2` changes quasi-free mean, variance, and Fano margin by the exact one-mode formulas

`q d`, `q(1-q)d^2`, and `q(d-(1-q)d^2)`,

with `q = Q_(k+1)(1-E_k)`.

## Paper proof

Contrast norm identity gives `E_k = Q_k / Q_(k+1)`. Since
`Q_(k+1) = Q_k + q_(k+1)`, rearrangement gives
`q_(k+1) = Q_(k+1)(1-E_k)`. Hermite-even quasi-free observables are finite sums of independent
mode contributions. Subtracting consecutive ranks isolates mode `k+1`; substitute recovered
occupation. No numerical computation is used.

## Lean formalization

Module:
GaloisForLFunctions.RHTower.HermiteContrastQuasiFreeIncrementUniversalityLaw.

Exact command:
lake env lean GaloisForLFunctions/RHTower/HermiteContrastQuasiFreeIncrementUniversalityLaw.lean.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
