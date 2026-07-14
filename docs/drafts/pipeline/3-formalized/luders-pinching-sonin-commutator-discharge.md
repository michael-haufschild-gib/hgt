# Lüders pinching discharges the Sonin cutoff-commutation premise

- **ID:** luders-pinching-sonin-commutator-discharge
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN
- **Source:** quantum measurement / finite-symmetry twirling
- **Statement:** For an idempotent cutoff `e`, the nonselective two-outcome Lüders pinching `D_e(X) = eXe + (1-e)X(1-e)` commutes with `e`; moreover `2 D_e(X) = X + (1-2e)X(1-2e)`, so it is exactly the normalized `Z₂` parity twirl whenever division by two is available.

## Goal

Discharge the explicit hypothesis `ccmCommutator X A.starProjection = 0` in the existing Sonin resolvent-commutator theorem by replacing an arbitrary observable `X` with its canonical cutoff pinching.  The output must be the full dressed Sonin commutator identity, not only a generic algebra lemma.

## Gates

- [x] 0 → 1 in-progress: exact physics identity and direct Lean consumer located
- [x] 1 → 2 fully-proven: complete symbolic proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem surface, direct module check, axiom audit
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

The measurement disturbance is exactly the pre-existing RHTower boundary pair:

`X - D_e(X) = crossBoundary e X + upperBoundary e X`.

This identity does not require idempotence.  It yields a hypothesis-free Sonin formula for the
original arbitrary observable: the pinched block contributes the exact Fourier-edge dressed term,
while the only additional term is the commutator of the native two-corner boundary residual with
the Sonin intersection projection.

For an idempotent cutoff, the same disturbance is the pure-dephasing double commutator

`X - D_e(X) = [e,[e,X]] = [[X,e],e]`,

and its two corners are

`crossBoundary e X = [X,e]e`,

`upperBoundary e X = -e[X,e]`.

Consequently one compactness premise on `[X,e]` makes both disturbance corners compact.

## Corpus application required for promotion

Instantiate `ccmCommutator_soninIntersectionProjection` at

`D_{A.starProjection}(X)`

and derive its complete resolvent-dressed boundary formula with no assumed commutation of `X` with the physical cutoff.  This strengthens the actual RHTower theorem surface; it is not promoted if it stops at the generic pinching identity.

Also retain the original arbitrary `X` and derive its exact Sonin commutator as the pinched dressed
formula plus the explicit `crossBoundary + upperBoundary` residual.  This is the direct interface
for the existing RHTower boundary and compactness consumers.

If both boundary corners are compact, prove that the residual commutator is compact and hence that
the arbitrary-observable Sonin commutator equals the pinched Fourier-edge dressed term in the
Calkin algebra, again without an exact cutoff-commutation premise.

Finally discharge those two compact-corner hypotheses from the single essential-commutation
premise `IsCompactOperator [X,A.starProjection]`.

On the concrete central Sonin carrier, also discharge the alternating-block norm premise from
`a > 0` using `norm_centralSoninAlternatingBlock_lt_one`.  The resulting theorem must expose only
the positive-cutoff geometry and essential physical-cutoff commutation.

## Formalization

`formal/GaloisForLFunctions/RHTower/SoninLudersPinching.lean` proves the parity-twirl identity,
the exact disturbance/boundary decomposition, cutoff commutation, vanishing of both pinched
boundary corners, the pinched Sonin commutator law, and the hypothesis-free boundary split for the
original arbitrary observable.  It additionally proves compactness of the boundary residual and
the resulting Calkin-level dressed formula under compactness of the two native cutoff corners.  The
pure-dephasing double-commutator and corner-factorization identities then strengthen this to a
one-premise Calkin theorem assuming only essential commutation of `X` with the physical cutoff.
The concrete specialization
`isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_cutoffCommutator` additionally
removes the strict-contraction premise by using the already proved central time-band geometry.

## Status

[PROVED IN LEAN] The directly touched module passes a single-threaded direct Lean check.  The
exported theorem audit reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
axioms.  This module contains no formal-lint proof debt; the current repository-wide lint is blocked
by three unrelated active `sorry`s in the concurrent `HTGeometry/DigammaRationalCarrier.lean`
lane.  The central specialization was added afterward during the user-mandated no-computation
phase and has been source-reviewed but deliberately not recompiled.  No full project build was run.

## Compact disturbance equivalence — 2026-07-14

The quantum-dephasing residual supplies a second directly consumable formulation of the remaining operator premise:

`IsCompactOperator (X - D_e(X)) ↔ IsCompactOperator [X,e]`.

The forward direction uses `[X,e] = [X-D_e(X),e]`, because `D_e(X)` commutes with the idempotent cutoff.  The reverse direction uses `X-D_e(X) = [[X,e],e]`.  This yields both a generic Sonin/Calkin consumer and a central-cutoff specialization whose sole operator premise is compact Lüders disturbance.  Unlike the earlier abstract pinching laws, this relation is applied immediately to the existing Sonin theorem surface.

The declarations were added during the user-mandated no-computation phase and are source-reviewed only.  No Lean process, build, lint, numerical experiment, or axiom audit was run; the previously validated part of this card remains distinct from these unvalidated additions.
