# FZZ one-sided radial / Hermitian chiral Ward no-go

- **ID:** FZZ-P-ONE-SIDED-HERMITIAN-CHIRAL-WARD-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · FZZ-P source-fixed complex-phase edge
- **Statement:** No additive Hermitian chiral FZZ reporter cancels the physical one-sided radial mixed Ward response.

## Goal

Retire the Hermitian-chiral completion of the FZZ-P chain:

`Hermitian chiral FZZ reporter + one-sided radial response -> vanishing complex mixed Ward -> p=0 -> passivity -> RH`.

## Gates

- [x] 0 → 1 in-progress: exact Hermitian source family and one-sided radial response identified from corpus.
- [x] 1 → 2 fully-proven: real-output/oriented-imaginary contradiction below.
- [x] Lean source proof: `RHTower.fzzOneSidedRadialHermitianChiralWardRouteKilled` elaborates with `lake env lean`.
- [ ] Final artifact audit: final leaf build and `#print axioms` are deferred because Lake artifact closure is stale and expands beyond permitted audit scope.
- [ ] 3 → 4 publication-ready: route-class obstruction, not an RH proof.

## Proof

Every FZZ Hermitian chiral observable has imaginary part zero, for all four real coefficients and all source vectors. The one-sided radial derivative has strictly negative imaginary part at every momentum. Hence their sum cannot vanish. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** `fzzOneSidedRadialHermitianChiralWardRouteKilled` universally quantifies the full Hermitian reporter matrix `[[a,b+ic],[b-ic,d]]`, including `c ≠ 0`, and every source vector.
- **Strongest positive survivor:** the Hermitian family still classifies source orientation; its nonzero imaginary off-diagonal *coefficient* distinguishes the conjugate Krein pair. But a Ward-cancelling source term must be non-Hermitian or enter through a non-additive current so that its value has positive imaginary part.
- **New insight:** chiral coefficient is not chiral response. The apparent complex source phase in a Hermitian observable is collapsed by self-adjointness, so it cannot supply FZZ-P’s missing complex Ward orientation.
- **Status:** dependency-closed Lean source theorem in `GaloisForLFunctions/RHTower/FZZCigarOneSidedRadialHermitianChiralWardNoGo.lean`, wired into `RHTower.lean`. It does not rule out non-Hermitian source dynamics or non-additive Ward laws.

## Log

- 2026-09-15 — additive Hermitian chiral FZZ-P completion retired.
