# Self-iteration nonclosure — no finite algebraic dynamical-closure law

- **ID:** ht-c03-self-iteration-nonclosure
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C03
- **Statement:** When composition is defined, generic `f ∈ HT_K` has no finite algebraic law closing the orbit `f, f∘f, f^{∘3}, …` (no finite set of equations forces `f^{∘n}` algebraic over earlier iterates and their jets).

## Goal
Block a **finite dynamical-closure handle** on the self-composition orbit — a finite machine predicting infinitely many iterates. Door: iteration is not differentiation, so this is a genuinely new handle axis (potential (B)-flavour).

## Door grade (hint)
**BRIDGE-likely but watch for genuine novelty:** iteration need not reduce to `∂`-algebra, so the elimination may fail to produce a differential polynomial — that failure would mark a real new direction.

## Approach
Elimination test: a closure law differentiated along the orbit gives relations among `(f, f', f∘f, (f∘f)', …)`; chain-rule expansion may or may not collapse to `P(f)≡0`. If it does → BRIDGE; if not → new. Methods: 4 change viewpoint, 5 make it visual (orbit as a machine), 6 ask what action is happening.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C03; meta-card C28 (minimal-handle collapse).

## Log
- 2026-06-20 — created in 0-backlog from bucket C03.
