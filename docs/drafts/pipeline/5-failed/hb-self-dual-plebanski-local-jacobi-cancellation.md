# HB self-dual Plebanski local-Jacobi cancellation

- **ID:** C-HB-J1
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` HB surviving radiative `++` causal-cut core
- **Statement:** The literal same-charge self-dual Plebanski exchange channels cancel locally under cyclic assembly by the deformed kinematic Jacobi identity.

## Goal

Attempted to close HB chain

`Plebanski source -> radiative ++ cut extinction -> fixed physical-clock source-FE covariance -> shared Ward cancellation -> RH`.

Peierls cyclicity already removes the stationary `+-` arm, and the common direct cubic jet cancels from the causal cut. A local Plebanski Jacobi cancellation would therefore have discharged the remaining radiative premise without tuning a receiver or assuming RH-equivalent covariance. The exact cyclic vertex calculation below rules this mechanism out.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: falsification and positive survivor have dependency-closed paper proofs
- [x] 2 → 3  formalized: Lean theorem `d4HBSelfDualSameChargeLocalJacobiCancellationRouteKilled`, targeted `lake build` green, axioms audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Hostile attack stopped at the first falsifier. On common physical transverse charge, corpus theorem `ads4SelfDualPlaneWaveVertex_sameTransverseCharge` gives

`V(p,q;h) = h²(p-q)²/2`,

independently of AdS curvature. Hence three local channels give

`h²((p-q)²+(q-r)²+(r-p)²)/2`.

For real momenta and `h != 0`, this vanishes exactly when `p=q=r`. The double-copy square destroys the alternating cancellation needed by a Jacobi-only proof.

Internal corpus basis: exact coordinate Plebanski bracket and plane-wave specialization; exact total third-order Schur source; direct-third-jet causal-cut rigidity; Peierls stationary-channel elimination; completed Eisenstein continuum and threshold necessity. External baseline: classical flat self-dual gravity has vanishing tree amplitudes beyond three points, while current AdS self-dual work establishes the deformed kinematic algebra and cubic vertex but not this theta-cusp black-hole causal-cut identity.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `d4HBSelfDualSameChargeCyclicVertex_eq_zero_iff`: local cyclic Plebanski assembly is zero iff all three affine momenta coincide. Nontrivial physical same-charge packets are therefore bright.
- **Strongest positive survivor:** exact curvature-independent graph-Laplacian identity `d4HBSelfDualSameChargeCyclicVertex_eq_energy`.
- **New insight:** self-dual integrability cannot supply HB radiative extinction at source-local level. Any surviving cancellation must be created by the complete nonlocal retarded-minus-advanced Green discontinuity, including continuum/threshold orientation, before left projection.
- **Status:** `[PROVED HERE] [LEAN-PROVED]`; module `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBSelfDualPlebanskiLocalJacobiNoGo`; primary-literature audit found flat-space higher-tree vanishing and AdS cubic kinematic algebra, but no same-charge theta-cusp cyclic zero-set classification.

## Log

- 2026-08-31 — promoted directly to 1-in-progress after corpus-derived proof-chain and falsifier audit.
- 2026-08-31 — falsified by exact graph-Laplacian survivor; formalized and moved to 5-failed.
