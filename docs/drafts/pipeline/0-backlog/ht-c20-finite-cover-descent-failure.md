# Finite-cover descent failure — no ramified coordinate change creates a handle

- **ID:** ht-c20-finite-cover-descent-failure
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C20
- **Statement:** A generic local HT germ does not become differentially algebraic after pullback to a finite algebraic cover of the independent variable; finite ramified changes of coordinate create no finite algebraic-differential handle.

## Goal
Block a **hidden finite cover** on which `f` simplifies. Door: algebraic functions simplify on finite covers; HT should resist this descent trick.

## Door grade (hint)
**BRIDGE-likely.** Pullback along `x=φ(t)`, `φ` algebraic, conjugates a differential polynomial; DA is preserved under finite covers, so descent cannot manufacture a handle without one upstairs.

## Approach
Elimination test: if `f∘φ` is DA over `K(t)` then `f` is DA over `K(x)` (DA stable under finite algebraic base change / Kolchin) ⇒ contradiction ⇒ BRIDGE. Methods: 3 reverse, 14 weaken, 18 right theorem (DA descent).

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C20; C30 (base enrichment — same relativity theme).

## Log
- 2026-06-20 — created in 0-backlog from bucket C20.
