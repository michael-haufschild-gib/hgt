# Transform-domain noncapture — no finite handle after Laplace/Mellin/Borel/Fourier

- **ID:** ht-c06-transform-domain-noncapture
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C06
- **Statement:** For a standard transform `T(f)` (Laplace, Mellin, Borel, Fourier, local variants), generic HT input does not become differentially algebraic in the dual variable, unless the kernel/domain encodes special information about `f`.

## Goal
Block a **handle that appears only after changing domains**. Door: transforms turn ODEs into algebraic/recurrence data; a generic HT object should resist becoming finite-handle by moving to a dual variable.

## Door grade (hint)
**BRIDGE-likely.** The standard transform intertwining `∂ ↔ ×ξ` maps a dual-variable differential polynomial back to one in `f`.

## Approach
Elimination test: use the operational rules (`T(f')=ξ T(f)−…` etc.) to pull a differential polynomial in `T(f)` back to one in `f`; if it lands ⇒ Hölder ⇒ BRIDGE. Survivors: transforms with no finite-order intertwiner. Methods: 4 change viewpoint, 17 change representation, 22 compare nearby false statements.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C06; C29 (resurgence — higher transform data).

## Log
- 2026-06-20 — created in 0-backlog from bucket C06.
