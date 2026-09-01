# Equimodular prime-dependent source--Gamma ghost rigidity

- **ID:** EG-NC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus seam `SourceGammaCentralModuleGhostRigidity` + `SourceGammaChannelPositiveHermitianScalarizationNoGo`
- **Statement:** Prime-dependent forward legs of equal nonzero norm sharing one reflected Gamma-Ward leg at primes 2 and 3 force neutral horizontal grade; arbitrary grade requires the exact norm distortion `(3/2)^(2t)`.

## Goal

Kill every finite/infinite-dimensional isometric or equimodular noncentral ghost producer in chain `two-prime source/Gamma ghost -> shared HB/FZZ-P/PW-B/RBH Ward endpoint -> RH`; identify prime-dependent radial distortion as sharp survivor.

## Gates

- [x] 0 -> 1  in-progress: corpus-grounded, source-pure, exact chain and failure mode fixed
- [x] 1 -> 2  fully-proven: norm comparison + sharp fitted converse
- [x] 2 -> 3  formalized: `sharedWardEquimodularPrimeDependentGammaGhostRouteKilled`; targeted build and axiom audit pass
- [ ] 3 -> 4  publication-ready: standalone paper

## Approach

Fit each Ward equation as `p^(2t) • u_p = v`; compare norms at `p=2,3`; cancel common nonzero norm; use injectivity of real exponential. Prove converse fitted family when equal-norm law is removed.

## No-go closure

- **Exact killing theorem/mechanism:** two Ward equations force `2^(2t)‖u₂‖ = 3^(2t)‖u₃‖`; equal nonzero norms force `t=0`.
- **Strongest positive survivor:** exact law `‖u₂‖/‖u₃‖=(3/2)^(2t)`; without equal norm, nonzero fitted witnesses exist for every `t`.
- **New insight:** direction mixing, arbitrary dimension, and nonlinear prime dependence are irrelevant unless source dynamics supplies prime-dependent radial distortion.
- **Status:** paper proof dependency-closed; Lean module `SourceGammaEquimodularPrimeDependentGhostRigidity`; direct check, targeted build, axiom audit pass. No matching theorem found in audited corpus or primary RH-operator literature through 2026-08.

## Log

- 2026-09-01 — conjecture frozen after corpus audit.
- 2026-09-01 — proved, formalized, and route class retired.
