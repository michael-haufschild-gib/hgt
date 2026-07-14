# Lüders pinching discharges the Sonin cutoff-commutation premise

- **ID:** luders-pinching-sonin-commutator-discharge
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** quantum measurement / finite-symmetry twirling
- **Statement:** For an idempotent cutoff `e`, the nonselective two-outcome Lüders pinching `D_e(X) = eXe + (1-e)X(1-e)` commutes with `e`; moreover `2 D_e(X) = X + (1-2e)X(1-2e)`, so it is exactly the normalized `Z₂` parity twirl whenever division by two is available.

## Goal

Discharge the explicit hypothesis `ccmCommutator X A.starProjection = 0` in the existing Sonin resolvent-commutator theorem by replacing an arbitrary observable `X` with its canonical cutoff pinching.  The output must be the full dressed Sonin commutator identity, not only a generic algebra lemma.

## Gates

- [x] 0 → 1 in-progress: exact physics identity and direct Lean consumer located
- [ ] 1 → 2 fully-proven: complete symbolic proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem surface, direct module check, axiom audit
- [ ] 3 → 4 publication-ready: standalone note with Lean certificate and physics interpretation

## Physics sources

- G. M. D'Ariano, P. Perinotti, and M. F. Sacchi, “Informationally complete measurements and group representation,” J. Opt. B 6 (2004), S487; finite symmetry averaging is used to project quantum data to invariant sectors.
- J. B. DeBrota and B. C. Stacey, “Lüders Channels and the Existence of Symmetric Informationally Complete Measurements,” arXiv:1907.10999.  The Lüders rule is treated explicitly as a quantum channel associated with a measurement.
- M. Larocca et al., “Theory for Equivariant Quantum Neural Networks,” PRX Quantum 5, 020328 (2024).  Its finite-group twirling map is an explicit projection onto equivariant data and includes a `Z₂` example.

## Exact relations

Let `e² = e` and set `s = 1 - 2e`.  Then

`D_e(X) = eXe + (1-e)X(1-e)`.

Idempotence gives

`e D_e(X) = eXe = D_e(X) e`,

so `[D_e(X),e] = 0` without any premise on `X`.  Expanding `sXs` gives the second value relation

`X + sXs = 2 D_e(X)`.

Thus the measurement channel and finite parity twirl are the same algebraic projector.

## Corpus application required for promotion

Instantiate `ccmCommutator_soninIntersectionProjection` at

`D_{A.starProjection}(X)`

and derive its complete resolvent-dressed boundary formula with no assumed commutation of `X` with the physical cutoff.  This strengthens the actual RHTower theorem surface; it is not promoted if it stops at the generic pinching identity.

## Status

[CONJECTURE] The relations are exact noncommutative polynomial identities.  Promotion waits for the direct Sonin consumer, a single-module Lean check, and a clean axiom audit.
