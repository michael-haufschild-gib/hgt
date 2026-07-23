# Affine Gamma–digamma–zeta–Xi arbitrary-window escape universality law

- **ID:** affine-gamma-digamma-zeta-xi-arbitrary-window-escape-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of arbitrary-window synchronized jet escape and arbitrary
  affine-scale Gamma/digamma hypertranscendence
- **Statement:** For independently chosen nonzero amplitudes and nonzero affine scales of Gamma
  and digamma, every finite derivative-order window larger than four times a finite dictionary
  dimension contains one order missed simultaneously by the affine Gamma tower, affine digamma
  tower, zeta tower, and completed-Xi tower.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean check pending
- [ ] 3 → 4 publication-ready: post-proof literature audit pending

## Corpus inputs

- `hypertranscendental_smul_gamma_affine`
- `hypertranscendental_smul_digamma_affine`
- `hypertranscendental_riemannZeta`
- `xi_hypertranscendental`
- `exists_common_iteratedDeriv_not_mem_of_card_mul_finrank_lt`

## Proof

`[PROVED HERE]` Nonzero amplitude and nonzero affine scale preserve hypertranscendence of Gamma
and digamma.  Hypertranscendence implies constant-coefficient differential transcendence, so the
two affine sources join zeta and completed Xi as a four-element source family satisfying the
generic synchronized finite-family escape theorem.  A window with cardinality greater than four
times the dictionary dimension therefore contains one derivative order at which all four source
derivatives lie outside the dictionary.  Shifts and scales of the two archimedean sources are
independent.  No computation is used.

## Strict gain over corpus endpoints

The existing synchronized arbitrary-window theorem fixes Gamma and digamma at unit scale and zero
shift.  The affine-scale theorem treats each source separately and has no finite-dictionary or
common-order conclusion.  Their closure proves synchronization uniformly over the full independent
affine orbits of both archimedean sources, while retaining zeta and Xi at the same missed order.

## Lean certificate

- Planned module:
  `GaloisForLFunctions.RHTower.AffineGammaDigammaZetaXiArbitraryWindowEscapeUniversalityLaw`
- Planned main theorem:
  `exists_synchronized_affine_gamma_digamma_zeta_xi_jet_escape_in_finset`

## Novelty protocol

No literature search occurred before the dependency-closed proof.  External collision search
starts only after exact Lean verification.

## Log

- 2026-07-23 — Terminal cross-folder scan exposed the affine-source/synchronized-window seam.
- 2026-07-23 — Dependency-closed proof completed from existing Lean endpoints.
