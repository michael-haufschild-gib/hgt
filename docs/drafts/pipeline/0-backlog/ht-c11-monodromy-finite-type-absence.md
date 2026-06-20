# Monodromy finite-type absence — no finite algebraic monodromy controller

- **ID:** ht-c11-monodromy-finite-type-absence
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C11
- **Statement:** For generic continuable `f ∈ HT`, analytic continuation produces no finite algebraic monodromy object: no finite branch cover, no finite permutation representation, no finite-dimensional algebraic monodromy group capturing all branches.

## Goal
Block a **finite topological/algebraic monodromy handle**. Door: algebraic and many DA functions have controlled continuation; a generic HT object should resist finite monodromy compression.

## Door grade (hint)
**BRIDGE-likely.** Finite-dimensional algebraic monodromy ⇒ a Picard–Vessiot / differential-Galois finite-dim structure ⇒ a linear ODE ⇒ excluded by HT.

## Approach
Elimination test: a finite-dim algebraic monodromy group is the differential-Galois group of a holonomic system ⇒ `f` D-finite ⇒ contradiction (synthesis §1). Survivors: continuation with infinite-dim but still "tame" monodromy — a real boundary case. Methods: 4 change viewpoint, 5 make it visual, 12 find an invariant.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C11; C10 (singularities), C19 (differential-Galois orbit).

## Log
- 2026-06-20 — created in 0-backlog from bucket C11.
