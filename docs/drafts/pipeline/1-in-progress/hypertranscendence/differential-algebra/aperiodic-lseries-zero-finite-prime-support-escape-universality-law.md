# Aperiodic L-series zero finite-prime support-escape universality law

- **ID:** aperiodic-lseries-zero-finite-prime-support-escape-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first contrapositive closure of `finitePrime_zero_periodic` and
  `AperiodicZeroAt`
- **Statement:** A right-half-plane aperiodic zero of a multiplicative, absolutely summable
  L-series forces its coefficient support to escape every finite prime sector.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact statement

## Corpus inputs

- `AperiodicZeroAt`
- `finitePrime_zero_periodic`

## Proof

`[PROVED HERE]` Let `a` be multiplicative and assume its L-series terms are norm-summable at every
point of the open right half-plane.  Fix an aperiodic L-series zero `s` with `0 < Re s`, and let
`P` be any finite set of primes.

If every nonzero coefficient index of `a` were `P`-factored, `finitePrime_zero_periodic` would
produce a positive period `T` such that every point

`s + k T i`, `k ∈ ℤ`,

were again an L-series zero.  This is exactly the vertical progression forbidden by
`AperiodicZeroAt`.  Therefore some nonzero coefficient index is not `P`-factored.  Since `P` was
arbitrary, no finite prime sector contains the coefficient support.  No computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.AperiodicLSeriesZeroFinitePrimeSupportEscapeUniversalityLaw`
- Main theorem:
  `RHTower.aperiodicLSeriesZero_forces_escape_every_finitePrimeSector`
- Source:
  `formal/GaloisForLFunctions/RHTower/AperiodicLSeriesZeroFinitePrimeSupportEscapeUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/AperiodicLSeriesZeroFinitePrimeSupportEscapeUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before exact Lean proof.  Post-proof searches covered finite-prime
Euler products, exact vertical periods of Dirichlet-series zeros, analytic almost periodicity, and
support consequences of aperiodic zeros.  Standard references give Euler factorization and the
literature studies almost-periodic zero sets, but no source found the exact contrapositive that one
aperiodic right-half-plane zero forces coefficient support outside every finite prime sector.

## Log

- 2026-07-23 — Shared-parent periodicity scan exposed the missing support-side contrapositive.
- 2026-07-23 — Exact theorem formalized, exact-file check passed warning-free, and umbrella import
  added.
- 2026-07-23 — Post-proof collision audit found adjacent Euler-product and almost-periodic
  Dirichlet-series theory, but no exact support-escape law.
