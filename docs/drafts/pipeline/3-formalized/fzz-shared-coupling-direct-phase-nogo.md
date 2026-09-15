# FZZ shared-coupling direct-phase no-go

- **ID:** FZZ-P-SHARED-COUPLING-DIRECT-PHASE-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · FZZ-P integrated mixed replica–momentum Ward edge
- **Statement:** The fully integrated shared-coupling FZZ source receiver cannot equal the unwrapped balanced external-Gamma phase under any affine momentum calibration.

## Goal

Retire the most direct apparent closure of the FZZ-P dynamical edge:

`shared-coupling source -> affine pointwise phase identity -> Ward-delay saturation -> passivity -> RH`.

The target is substantive because the source receiver is an actual integrated first-order FZZ insertion, and the phase endpoint already has the closed chain

`vacuum-delay saturation on parity-Mellin divisor modes ↔ FZZ passivity ↔ RH`.

## Gates

- [x] 0 → 1 in-progress: source receiver, phase endpoint, and exact chain stated.
- [x] 1 → 2 fully-proven: parity-versus-strict-order contradiction below.
- [ ] 2 → 3 final artifact audit: `RHTower.not_exists_fzzFermiSharedCoupling_affine_balancedPhase_bridge` source-elaborates with `lake env lean`; leaf build was intentionally stopped after it began replaying a broad stale dependency closure, contrary to the short-audit constraint.
- [ ] 3 → 4 publication-ready: route-class obstruction, not an RH proof.

## Proof

For a proposed equality

`S_v(aP+b) = Φ(sqrt(2) P)`,

evaluate at `P=0`.  The phase has value zero, and the source theorem `S_v(p)=0 ↔ p=0` forces `b=0`.  The source theorem `S_v(-p)=S_v(p)` then equates the values at `P=1` and `P=-1`.  But `Φ` is strictly increasing, so its values at `sqrt(2)` and `-sqrt(2)` differ.  Contradiction. `[PROVED HERE]`

The positive survivor is coordinate-compatible: the existing source law `S_v(p)=0 ↔ p=0` and existing twist law `Im τ(rho)=0 ↔ Re(rho)=1/2` compose to `S_v(Im τ(rho))=0 ↔ Re(rho)=1/2`. This does not derive the physical source-frame evaluation and is not promoted as new knowledge.

## No-go closure

- **Exact killing theorem/mechanism:** `not_exists_fzzFermiSharedCoupling_affine_balancedPhase_bridge` rules out every level/coupling `v` and every affine calibration `aP+b` of the direct pointwise receiver identity.
- **Strongest positive survivor:** canonical zero loci are compatible: `S_v(p)=0 ↔ p=0` and `Im τ(rho)=0 ↔ Re(rho)=1/2`. A surviving FZZ-P law must derive the literal physical source-frame evaluation, or identify a non-pointwise/mode-dependent Ward current; it cannot assert equality of the full receivers.
- **New insight:** parity is a rigid compatibility test between two independently exact FZZ objects. It replaces an undifferentiated source-to-phase attachment problem with the narrower source-frame/zero-locus transport problem.
- **Status:** closed Lean source theorem in `GaloisForLFunctions/RHTower/FZZCigarFermiSharedCouplingDirectPhaseNoGo.lean`, wired into `RHTower.lean`; source elaboration passed. Final leaf-olean and axiom audit remain pending because the requested leaf build replayed a broad stale closure and was stopped. It does not claim that the physical CFT realizes the shared-coupling diagnostic, nor does it exclude a genuine integrated source Ward law.

## Log

- 2026-09-15 — direct affine pointwise source-to-phase transmutation retired; zero-locus transport remains live. Source Lean check passed; broad stale leaf-build replay stopped.
