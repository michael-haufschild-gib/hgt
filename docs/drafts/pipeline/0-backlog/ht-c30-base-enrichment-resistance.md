# Base-enrichment resistance — innocent base extensions cannot destroy HT

- **ID:** ht-c30-base-enrichment-resistance
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C30
- **Statement:** Enlarging the base by finitely many DA functions, algebraic extensions, constants, or finite-cover coordinate changes does not make generic `f ∈ HT_K` differentially algebraic; any enlargement that destroys HT must already contain a differentially transcendental object nontrivially encoding `f`.

## Goal
Pin **how much the base must be enriched before HT collapses** — separating innocent enrichments from extensions that import the object itself. Door: makes the note's "relative to the base" caveat (§4) a precise boundary claim.

## Door grade (hint)
**BRIDGE-likely.** DA-by-DA and finite-algebraic enrichments preserve differential transcendence (Kolchin: adjoining DA elements does not lower difftrdeg of a differentially transcendental element) — so collapse requires importing a transcendental encoding of `f`.

## Approach
Elimination test: if `f` becomes DA over `K⟨a_1,…,a_k⟩` with each `a_i` DA over `K`, then `f` is DA over `K` (difftrdeg additivity) ⇒ contradiction ⇒ BRIDGE; characterize the "guilty" enrichments as exactly those encoding `f`. Methods: 3 reverse, 18 right theorem (Kolchin additivity), 23 classify boundary cases.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C30; C20 (finite-cover descent — special case).

## Log
- 2026-06-20 — created in 0-backlog from bucket C30.
