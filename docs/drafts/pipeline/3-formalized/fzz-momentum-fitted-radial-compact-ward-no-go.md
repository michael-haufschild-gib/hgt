# FZZ momentum-fitted radial/compact Ward no-go

- **ID:** FZZ-P-MFRCW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarMarkedRadialReplicaResponse`; `FZZCigarParityTwoMarkedSourceContact`
- **Statement:** At fixed radial and level parameters, every momentum has exactly one compact annular log-separation cancelling the factorized radial plus opposite-winding mixed Ward response.

## Goal

Kill `momentum-fitted radial/compact cancellation → zero momentum → torus passivity → Mellin completeness → RH` without discarding fractional radial backreaction or cross-charge weighting.

## Gates

- [x] 0 → 1: corpus search found exact radial and compact source factors; no prior joint theorem.
- [x] 1 → 2: dependency-closed proof below.
- [x] 2 → 3: Lean theorem `fzzMomentumFittedRadialCompactWardRouteKilled`; direct check, targeted leaf build, axiom audit, and lint passed.
- [ ] 3 → 4: external review/publication.

## Paper proof `[PROVED HERE]`

Let `R(p)` be real part of exact radial paired mixed response. At physical level `k=2+exp(u)`, opposite-winding contact is

`C(k)=-k/2-k²/(2(k-2))<0`.

Exact compact annular response is `C(k)L`. Hence total factorized defect is `R(p)+C(k)L`, and since `C(k)≠0`, it vanishes at exactly

`L=-R(p)/C(k)`.

Thus existential cancellation holds for every `p`, including `p=1`, so it cannot characterize `p=0`. At `p=0`, exact radial zero classification reduces cancellation to `L=0`.

## Consequence

Momentum-fitted compact geometry is dead. Survivor is exact unique cancelling separation. Remaining FZZ-P producer must fix separation and phase frame independently of target momentum, then derive cancellation from complete neutral source rather than existential fitting.

## Novelty check

Exact corpus/mechanism searches found no prior theorem joining these two source factors. Targeted arXiv search through August 2026 found the replica-winding source formulas in [Halder--Jafferis](https://arxiv.org/abs/2402.00932), but no unique radial/compact cancellation classification or this route no-go.

## Lean

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityMomentumFittedRadialCompactWardNoGo.lean`, wired into `RHTower.lean`. Direct Lean check: 5.1 s. Targeted leaf build: 19.3 s. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Formal lint and whitespace check passed. No full/umbrella build, computation, new axiom, or altered frontier map.
