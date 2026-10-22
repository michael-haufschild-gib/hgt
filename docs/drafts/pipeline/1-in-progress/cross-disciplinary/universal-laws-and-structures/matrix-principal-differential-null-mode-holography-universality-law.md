# Matrix-principal differential null-mode holography universality law

- **ID:** matrix-principal-differential-null-mode-holography-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of flat principal-symbol spectral holography and the DSS
  determinant/kernel criterion
- **Statement:** For every flat complex matrix principal law with a regular reference direction,
  a target law direction is differentially dependent exactly when every normalized filtration
  layer has a nontrivial null mode.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `matrixPrincipalLowerLaw_spectralDifferentialHorizon`
- `matrix_nontrivial_kernel_iff_det_eq_zero`
- `matrixPrincipalSpectralPolynomial_eq_first`
- `Matrix.eval_charpoly`

## Proof

`[PROVED HERE]` Flat spectral holography makes every normalized characteristic polynomial equal
to its layer-zero polynomial.  Differential dependence is equivalent to zero being a root of
that polynomial.  Evaluating a characteristic polynomial at zero gives the determinant of the
negative normalized symbol; its vanishing is equivalent to vanishing of the symbol determinant.
The DSS kernel criterion converts this determinant condition into existence of a nonzero vector
annihilated by the normalized symbol.  Since the characteristic polynomial is conserved, the
null-mode condition holds at every layer.  Conversely, a null mode at layer zero forces the
zero-root condition and hence differential dependence.  No computation is used.

## Strict gain over corpus endpoints

The principal-symbol endpoint detects dependence only as a first-layer spectral zero and
conserves characteristic polynomials abstractly.  The DSS endpoint exposes a null vector for one
singular complex matrix.  Their closure proves that the complete differential horizon is an
all-layer null-mode horizon, despite the null vectors themselves being allowed to vary by layer.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.MatrixPrincipalDifferentialNullModeHolographyUniversalityLaw`
- Main theorem:
  `matrixPrincipalLowerLaw_differentialDependent_iff_everyLayer_nontrivialNullMode`
- Source:
  `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalDifferentialNullModeHolographyUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/HTGeometry/MatrixPrincipalDifferentialNullModeHolographyUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
differential-algebraic dependence, flat principal-symbol spectra, and filtration-wide null modes
found no exact collision.  Closest inspected primary sources treat Fox-derivative criteria for
differential dependence and constant-rank differential-operator annihilators, but not conserved
normalized characteristic polynomials of differential-law filtrations:

- B. Duisengalieva and U. Umirbaev, *Differential algebraic dependence and Novikov dependence*,
  <https://arxiv.org/abs/2001.00383>.
- F. Gmeineder and S. Schiffer, *Natural annihilators and operators of constant rank over
  ℂ*, <https://arxiv.org/abs/2203.10355>.

## Log

- 2026-07-23 — Cross-folder terminal scan exposed flat spectral holography versus the DSS
  determinant/kernel certificate.
- 2026-07-23 — Dependency-closed proof completed and scratch-checked.
- 2026-07-23 — Exact theorem checked warning-free and wired into the HTGeometry umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
