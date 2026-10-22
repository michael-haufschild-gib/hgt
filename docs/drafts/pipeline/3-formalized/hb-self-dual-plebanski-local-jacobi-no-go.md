# HB self-dual Plebanski local-Jacobi no-go

- **ID:** T-HB-J1-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** failed route `../5-failed/hb-self-dual-plebanski-local-jacobi-cancellation.md`
- **Statement:** The cyclic sum of three literal same-charge self-dual AdS4 Plebanski vertices is a curvature-independent graph-Laplacian energy and, at nonzero real charge, vanishes exactly on the momentum diagonal.

## Goal

Kill HB mechanism

`local self-dual kinematic Jacobi -> radiative ++ cut extinction`.

This removes local Plebanski integrability as the missing HB producer. It sharpens surviving burden to a genuinely nonlocal causal Green/resolvent identity carrying continuum/threshold phase before projection.

## Gates

- [x] 0 → 1  in-progress: exact corpus source and HB proof chain identified
- [x] 1 → 2  fully-proven: dependency-closed graph-energy identity and zero-set proof
- [x] 2 → 3  formalized: Lean theorem `d4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled`
- [ ] 3 → 4  publication-ready: standalone note not prepared

## Result

For all `curvature : ℂ`, real `p,q,r,h`, and `h != 0`,

`V(p,q;h)+V(q,r;h)+V(r,p;h)=0 <-> p=q and q=r`,

where `V` is the corpus's literal curvature-corrected self-dual AdS4 plane-wave gravity vertex. Exact positive survivor:

`V(p,q;h)+V(q,r;h)+V(r,p;h)`

`= h²((p-q)²+(q-r)²+(r-p)²)/2`.

AdS curvature cancels identically because the legs share transverse charge. Thus double-copy squaring turns the alternating kinematic bracket into positive graph energy rather than a Jacobi cancellation.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Capstone: `d4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo.lean` — PASS
- Targeted build: `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo` — PASS (`11214/11214`)
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Global lint: new module reachable; unrelated concurrently created modules remain unwired.

## Novelty and consequence

Internal corpus had exact Plebanski vertex, its plane-wave factorization, nonzero same-charge Mellin source, and abstract third-order causal-cut reduction, but not cyclic graph-energy classification. Primary literature establishes flat self-dual higher-tree vanishing and AdS4 deformed kinematic cubic algebra; audit found no corresponding physical same-charge cyclic vertex classification.

Consequence for HB: local source Jacobi identity is terminal. Remaining source premise must derive a nonlocal chiral identity for the complete retarded-minus-advanced radiative Green jump, retaining zero-frequency/threshold and completed continuum sectors.

## Log

- 2026-08-31 — `[PROVED HERE] [LEAN-PROVED]`; route killed and positive survivor formalized.
