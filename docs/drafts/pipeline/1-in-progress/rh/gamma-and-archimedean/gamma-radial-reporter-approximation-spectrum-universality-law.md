# Gamma radial-reporter approximation-spectrum universality law

- **ID:** gamma-radial-reporter-approximation-spectrum-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of the Gamma factorial reporter kernel and the
  Hilbert–Schmidt approximation-number bridge
- **Statement:** At every radial scale and every finite coordinate cutoff, the approximation number
  of the Gamma factorial reporter is bounded by the square root of the exact omitted factorial
  coefficient energy.  Hence its approximation spectrum tends to zero at every scale; at every
  nonzero scale this quantitative decay coexists with injectivity, dense range, and nonsurjectivity.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `gammaRadialReporterKernel_isHS`
- `gammaRadialReporter`
- `norm_gammaRadialReporter_single`
- `gammaRadialReporter_compact_injective_dense_nonsurjective`
- `approxNumber_le_hsTail`
- `tendsto_approxNumber_zero_of_isHilbertSchmidt`

## Proof

`[PROVED HERE]` Realize the radial reporter as the operator of its diagonal
Hilbert–Schmidt kernel.  Apply the corpus Hilbert–Schmidt truncation theorem in the canonical
`ℓ²(ℕ)` basis.  For every finite set `s`,

`a_|s|(Reporter_ρ)
  ≤ sqrt(∑_{n∉s} ‖Reporter_ρ e_n‖²)`.

The exact single-coordinate reporter theorem identifies
`‖Reporter_ρ e_n‖ = ‖ρ^(n+1) gammaPeriodicConormalCoefficient n‖`, giving the claimed explicit
factorial tail.  The general Hilbert–Schmidt approximation theorem makes the whole approximation
sequence tend to zero.  At `ρ ≠ 0`, combine this with the existing compact/injective/dense/proper
range classification.  No numerical computation is used.

## Strict gain over corpus endpoints

The Gamma reporter endpoint proves Hilbert–Schmidt compactness and its range classification but
does not expose approximation numbers or a finite-rank error budget.  The abstract operator bridge
controls arbitrary Hilbert–Schmidt operators but does not identify Gamma coefficients.  Their
closure gives a scale-uniform quantitative spectrum law with the exact omitted factorial energy.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.GammaRadialReporterApproximationSpectrumUniversalityLaw`
- Main theorem:
  `gammaRadialReporter_completeApproximationSpectrumUniversality`
- Source:
  `formal/GaloisForLFunctions/RHTower/GammaRadialReporterApproximationSpectrumUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/GammaRadialReporterApproximationSpectrumUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for Gamma
factorial diagonal operators, Hilbert–Schmidt approximation numbers, and factorial singular-value
tails found no exact collision.  Closest inspected primary sources study different operator
families:

- M. Putinar and J. E. Tener, *Singular values of weighted composition operators and second
  quantization*, <https://arxiv.org/abs/1612.03970>, bounds approximation numbers for Hardy-space
  weighted composition and restriction operators, not the Gamma factorial reporter.
- G. Lechner, D. Li, H. Queffélec, and L. Rodríguez-Piazza, *Approximation numbers of weighted
  composition operators*, <https://arxiv.org/abs/1612.01177>, derives decay laws for weighted lens
  maps, not exact omitted-coordinate factorial-energy bounds.
- J. Prochno and M. Strzelecki, *Approximation, Gelfand, and Kolmogorov numbers of Schatten class
  embeddings*, <https://arxiv.org/abs/2103.13050>, treats finite-dimensional Schatten embeddings,
  not a compact injective dense-range Gamma reporter on `ℓ²`.

## Log

- 2026-07-23 — Exact shared-symbol scan connected the Gamma radial reporter kernel to the
  coordinate-free Hilbert–Schmidt approximation bridge.
- 2026-07-23 — Dependency-closed cutoff-tail and approximation-decay proof completed.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
