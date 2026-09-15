# FZZ one-sided radial / scalar renormalized-plane Ward no-go

- **ID:** FZZ-P-ONE-SIDED-REAL-RENORMALIZED-PLANE-WARD-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · FZZ-P full integrated mixed replica–momentum Ward edge
- **Statement:** No scalar-real first-exponent derivative of the counterterm-preserving plane source, at finite cutoff or at its finite-part limit, cancels the physical one-sided radial Ward response.

## Goal

Retire the scalar renormalized-source branch of the FZZ-P chain:

`one-sided radial response + real renormalized plane derivative -> vanishing mixed Ward -> p=0 -> passivity -> RH`.

## Gates

- [x] 0 → 1 in-progress: literal counterterm-preserving source and one-sided response identified from corpus.
- [x] 1 → 2 fully-proven: complex-orientation contradiction below.
- [x] Lean source proof: `RHTower.fzzOneSidedRadialRealRenormalizedPlaneWardRouteKilled` elaborates with `lake env lean`.
- [ ] Final artifact audit: final leaf build and `#print axioms` are deferred because Lake artifact closure is stale and expands beyond permitted audit scope.
- [ ] 3 → 4 publication-ready: route-class obstruction, not an RH proof.

## Proof

The physical one-sided radial derivative has strictly negative imaginary part at every momentum. Both literal plane terms are derivatives of real-valued functions, hence embed in `ℂ` with zero imaginary part. Their sum therefore cannot be zero, uniformly in every radial, continuation, and cutoff parameter. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** `fzzOneSidedRadialRealRenormalizedPlaneWardRouteKilled` covers (i) every finite `fzzScreeningPlaneCorrectedCutoff` first-exponent derivative retaining both counterterms and (ii) every corresponding `fzzScreeningPlaneFinitePart` derivative after independent cutoff removal.
- **Strongest positive survivor:** a source-fixed *complex*, non-scalar and cross-depth coherent Ward term could supply the required positive imaginary component. The theorem neither constructs nor rejects it.
- **New insight:** renormalization of a real scalar source changes finiteness but cannot produce Ward orientation. The missing FZZ-P law is therefore not an improved finite-part formula; it must alter the source object or its interaction arena.
- **Status:** dependency-closed Lean source theorem in `GaloisForLFunctions/RHTower/FZZCigarOneSidedRenormalizedPlaneWardNoGo.lean`, wired into `RHTower.lean`. It deliberately does not cover complex phases, support motion, or nonfactorized all-depth source dynamics.

## Log

- 2026-09-15 — scalar-real renormalized-plane mixed-Ward branch retired.
