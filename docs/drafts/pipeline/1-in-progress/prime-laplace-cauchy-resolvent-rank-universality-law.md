# Prime-Laplace Cauchy-resolvent rank universality law

- **ID:** prime-laplace-cauchy-resolvent-rank-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of prime source-translation transport and transported
  prime-log Cauchy quotient rank
- **Statement:** The Laplace resolvent of the weighted prime source-translation orbit is exactly
  the negative transported prime-log Cauchy section at the reflected spectral parameter.
  A canonical right-half-plane family of these resolvents is linearly independent modulo ordinary
  prime `ℓ²` at every finite cardinality; consequently no finite-dimensional source can repair all
  canonical resolvents.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `hasSum_primeLaplaceRawJet_translate`
- `primeLaplaceRawJet`
- `primeLogTransportedCauchySection`
- `primeLogTransportedCauchyClass_linearIndependent`
- `primeLogSquareSummable`

## Proof

`[PROVED HERE]` The source-translation theorem says that the raw prime jet at `log p`, translated
by real time `t`, has eigenvalue `p⁻ᵗ`.  Weight this orbit by
`sqrt(p^(2b-1))`.  For any complex Laplace parameter `z` with `Re(z)>0`, its `p`-coordinate is

`∫₀∞ exp(-zt) sqrt(p^(2b-1)) p⁻ᵗ dt`.

Since `p⁻ᵗ = exp(-t log p)` and `Re(z+log p)>0`, the exponential integral is

`sqrt(p^(2b-1)) / (z+log p)
  = -primeLogTransportedCauchySection b (-z) p`.

Choose `z_j=(j+1)-i`.  Then `Re(z_j)>0`, while the reflected Cauchy nodes
`-z_j=-(j+1)+i` are distinct and lie in the upper half-plane.  Existing finite-packet
nonsummability therefore makes their quotient classes linearly independent for every finite
cardinality.  Multiplication by `-1` preserves independence, so the Laplace-resolvent classes are
also independent.  Pulling arbitrary finite subfamilies back through a proposed repair map gives
more independent source vectors than its finite dimension, a contradiction.  No numerical
computation is used.

## Strict gain over corpus endpoints

The source-transport endpoint identifies `p⁻ᵗ` as the exact translation eigenvalue but does not
compute its spectral resolvent.  The Cauchy-rank endpoint proves infinite quotient rank for abstract
Cauchy sections but does not identify them as resolvents of the prime source semigroup.  Their
closure gives the missing spectral dictionary and transfers infinite quotient rank to an explicit
right-half-plane Laplace family.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.PrimeLaplaceCauchyResolventRankUniversalityLaw`
- Main theorem:
  `primeLaplaceCauchyResolvent_completeRankUniversality`
- Source:
  `formal/GaloisForLFunctions/RHTower/PrimeLaplaceCauchyResolventRankUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/PrimeLaplaceCauchyResolventRankUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for prime
translation semigroups, Laplace resolvents, prime-log Cauchy kernels, and quotient rank found no
exact collision.  Closest inspected primary sources cover separate pieces:

- H. Glöckner, L. G. Lucht, and Š. Porubský, *General Dirichlet series, arithmetic convolution
  equations and Laplace transforms*, <https://arxiv.org/abs/0712.3172>, treats Laplace transforms
  on additive semigroups and general Dirichlet series, but not prime-coordinate translation
  resolvents or quotient-rank obstructions.
- C. K. Sahu, *Multipliers of the Hilbert spaces of Dirichlet series*,
  <https://arxiv.org/abs/2301.06413>, studies weighted Dirichlet kernels and multiplier algebras,
  but not the reflected `1/(z+log p)` resolvent family modulo prime `ℓ²`.
- C. K. Sahu, *On the abscissas of a Dirichlet series and its subseries supported on prime
  factorization*, <https://arxiv.org/abs/2503.23349>, studies prime-factor-supported abscissas for
  diagonal Dirichlet kernels, not finite-rank repair impossibility for prime-semigroup resolvents.

## Log

- 2026-07-23 — Exact shared-symbol scan exposed `primeLogSupport` as the bridge between the
  prime source-translation eigenlaw and transported Cauchy quotient rank.
- 2026-07-23 — Dependency-closed Laplace-transform and finite-rank obstruction proof completed.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
