# Finite spectral Hankel dimension boundary

- **ID:** finite-spectral-hankel-dimension-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Register:** `[SEARCH] [BRIDGE] [CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`
- **Source:** finite quantum clocks, Hamiltonian identification, Prony/matrix-pencil realization,
  finite-rate-of-innovation signals, and finite atomic moment theory
- **Statement:** A `d`-line spectral moment clock, and every pointwise or local finite-coordinate
  limit whose width remains bounded by `d`, has zero Hankel determinant in size `d + 1`; hence
  any infinite-support moment clock and every RH-compatible prime--archimedean source clock require
  spectral width escaping every fixed bound.

## Goal

Turn the clock-observability motif into an exact dimension obstruction that is useful independently
of hypertranscendence.  The observed values, not a proposed temporal flow, determine a Hankel
matrix.  Its rank detects whether those observations can come from a uniformly finite spectral
model.  This packages a standard realization-theoretic law directly against the existing strict
Hankel and prime--archimedean determinant interfaces.

## Gates

- [x] 0 → 1 in-progress: the finite spectral observable and fixed-width local closure are explicit
- [x] 1 → 2 fully-proven: the node polynomial supplies a nonzero Hankel-kernel vector; determinant
  continuity passes the obstruction through pointwise and local finite-coordinate limits
- [x] 2 → 3 formalized: both exact module targets are cached and both touched source files pass
  direct Lean checks
- [ ] 3 → 4 publication-ready: known parent theory; no standalone novelty claim

## Formalized content

### General HTGeometry layer

- `finiteSpectralMoment`
- `SpectralWidthAtMost`
- `FixedSpectralWidthLocalClosure`
- `momentHankelMatrix_mulVec_nodePolynomial_eq_zero`
- `det_momentHankelMatrix_finiteSpectralMoment_succ_eq_zero`
- `det_momentHankelMatrix_succ_eq_zero_of_spectralWidthAtMost`
- `det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidth_tendsto`
- `det_momentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure`
- `not_fixedSpectralWidthLocalClosure_of_det_ne_zero`
- `not_fixedSpectralWidthLocalClosure_of_infiniteSupport`

### Prime--archimedean RHTower consumer

- `PrimeArchFixedSpectralWidthLocalClosure`
- `primeArchSourceMomentHankelMatrix_eq_momentHankelMatrix`
- `det_primeArchSourceMomentHankelMatrix_succ_eq_zero_of_fixedSpectralWidthLocalClosure`
- `not_primeArchFixedSpectralWidthLocalClosure_of_det_ne_zero`
- `not_primeArchFixedSpectralWidthLocalClosure_zero`
- `not_primeArchFixedSpectralWidthLocalClosure_of_riemannHypothesis`

## Corpus value

1. `not_fixedSpectralWidthLocalClosure_of_det_ne_zero` discharges every negated fixed-width clock
   hypothesis from one existing nonzero Hankel determinant.
2. `not_fixedSpectralWidthLocalClosure_of_infiniteSupport` composes directly with the existing
   measure-producing HTGeometry routes and needs no hypertranscendence assumption.
3. At the prime--archimedean source, any independently proved determinant nonvanishing in size
   `d + 1` now excludes every signed `d`-line approximation, hence every positive/KMS subclass of
   that width.
4. Under RH, all fixed widths are excluded.  Therefore the existing finite positive-atomic/KMS
   local-closure criterion cannot be realized inside one fixed finite clock dimension; its witness
   dimensions must escape every bound.
5. The theorem is broader than HT: it applies to arbitrary real sequences, finite atomic measures,
   inverse-source data, linear realizations, and spectral time traces.  HT is one possible source of
   rich observations, not a premise of the dimension law.

## RH verdict

This does not revive `../5-failed/finite-spectral-rank-rh-selector.md`.  That retired route concerned
prime-log source frequencies or height-projected divisor spectra and could not see transverse zero
location.  The present theorem concerns Hankel rank of the canonical moment values already used by
the scalar RH criterion.

The immediate RH value is constraint and hypothesis discharge:

- it kills every fixed-dimensional quantum-clock/KMS ansatz for the full source;
- it tells constructive local-closure routes that unbounded dimension is mandatory;
- it converts any new independent finite determinant nonvanishing theorem into an unconditional
  exclusion of the corresponding finite width.

It is not yet a source producer.  The all-width conclusion from determinant positivity is currently
conditional on RH because that positivity hierarchy is RH-equivalent.  Progress toward RH would
require physics to supply an independent positivity or nonvanishing mechanism for the source
moments, not another finite-rank restatement.

## Physics and realization provenance

- Berg--Szwarc, *A determinant characterization of moment sequences with finitely many
  mass-points*, arXiv:1405.7267: finite atomic support is characterized by the terminating Hankel
  determinant pattern.
- Cooper--Fickes, *Recurrence Ranks and Moment Sequences*, arXiv:2101.00302: finite atomic moments,
  linear recurrences, Hankel factorizations/rank, and rational generating functions are equivalent
  realization interfaces.
- Mendes--Brito--Soares-Pinto, *Quantum Time and the Time-Dilation induced*, arXiv:2407.00161:
  finite-dimensional quantum-clock transition amplitudes are finite spectral sums, while the
  continuous orthogonal clock limit requires dimension tending to infinity.
- Zhang--Sarovar, *Quantum Hamiltonian identification from measurement time traces*,
  arXiv:1401.5780: Hamiltonian parameters are reconstructed from restricted observable time traces
  by system-realization methods.
- Steffens--Rebentrost--Marvian--Eisert--Lloyd, *An efficient quantum algorithm for spectral
  estimation*, arXiv:1609.08170: matrix-pencil recovery targets finite sums of exponentially damped
  sinusoids.
- Deng--Yang--Qian, *A Moment--Hankel Rank Method for Identifying the Number of Point Sources in
  the Heat Equation*, arXiv:2606.21815: the same finite exponential-sum/Hankel-rank law counts point
  sources from boundary observations.

## Scope

The Lean theorem uses arbitrary real masses and nodes and therefore proves a stronger no-go than
the positive-measure physics applications require.  It asserts determinant singularity and its
stability under fixed-width local closure; it does not assert stable numerical rank recovery under
noise, convergence of individual nodes or masses, or any implication from hypertranscendence to
transverse zero location.
