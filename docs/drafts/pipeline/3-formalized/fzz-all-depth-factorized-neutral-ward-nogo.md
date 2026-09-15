# FZZ all-depth factorized neutral-Ward no-go

- **ID:** FZZ-P-NEUTRAL-ALLDEPTH-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · FZZ-P integrated mixed replica–momentum Ward edge
- **Statement:** Neutrality, nonzero activation at every screening depth, and a source-fixed factorized opposite-winding scalar response cannot by themselves select the Abel–Jacobi wall.

## Goal

Retire the factorized all-depth shortcut in the FZZ-P chain:

`neutral screening data -> scalar integrated Ward selector -> divisor passivity -> RH`.

The result does not evaluate the literal torus kernel or settle FZZ-P. It identifies the missing physical content needed for a valid producer.

## Gates

- [x] 0 → 1 in-progress: source-exact factors and route target stated.
- [x] 1 → 2 fully-proven: explicit every-depth-active unconditional cancellation model below.
- [x] 2 → 3 formalized: `RHTower.no_fzzNeutralAllDepthFactorizedTwistedWardResponse_wall_selector`; isolated module audit green.
- [ ] 3 → 4 publication-ready: not a standalone RH result.

## Approach

Use literal neutral coefficients `c_n = μ^(2n)/(n!)²`, which are nonzero for `μ ≠ 0`, and the exact marked opposite-winding scalar prefactor `2*k*δ/(k-2)`. Set

`z_0 = 1`, `z_(n+1) = (1/2 - 1)(1/2)^n`, and `K_n = z_n / c_n`.

The kernel is fixed once `μ` is fixed; it has no twist or replica-point dependence.

## Proof

The geometric tail has sum `(1/2 - 1) (1 - 1/2)^(-1) = -1`, so `Σ z_n = 0`. Every `z_n` is nonzero. Since `c_n K_n = z_n`, every literal weighted depth contribution is nonzero, the all-depth sum is unconditionally convergent, and the factorized Ward response vanishes identically. Its values at twist `0` and `I` coincide, so no predicate of that scalar response can characterize `Im(twist)=0`. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** `no_fzzNeutralAllDepthFactorizedTwistedWardResponse_wall_selector` gives a fixed-support countermodel with all neutral depths active and a zero full response at off-wall twist.
- **Strongest positive survivor:** literal FZZ cross-charge dynamics must impose a source-derived cross-depth phase/coherence noncancellation law, or else support motion/nonfactorization before Jacobian integration. Neutrality and per-depth nonvanishing are insufficient.
- **New insight:** completeness of the neutral tower is not an antidote to cancellation; it adds a global coherence obligation. This sharpens the frontier map’s full mixed Ward problem by excluding every proof that uses only factorization plus all-depth activation.
- **Status:** dependency-closed Lean theorem in `GaloisForLFunctions/RHTower/FZZCigarParityNeutralAllDepthFactorizedWardNoGo.lean`. It is a route-class model, not an assertion that the physical torus kernel is the constructed kernel.

## Log

- 2026-09-15 — factorized all-depth neutral-screening producer retired; phase-coherent cross-depth kernel law remains the live FZZ-P target.
