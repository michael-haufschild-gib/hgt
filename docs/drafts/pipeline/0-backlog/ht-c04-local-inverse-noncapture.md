# Local inverse noncapture — no finite differential equation for the inverse germ

- **ID:** ht-c04-local-inverse-noncapture
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C04
- **Statement:** If a generic analytic `f ∈ HT_K` has a local inverse `g=f^{-1}`, then `g` satisfies no finite algebraic-differential relation over the inverse-side base, except degenerately when the base already encodes `f`.

## Goal
Rule out a **finite handle on the inverse germ**. Door: inversion is not a differential-rational expression in `f`, so closure principles do not settle it — a distinct handle.

## Door grade (hint)
**BRIDGE-likely.** A small handle on `g` should pull back through `f=g^{-1}` to a hidden handle on `f`.

## Approach
Elimination test: from `f(g(y))=y` differentiate to express `g',g'',…` in `f`-jets at `g`; a differential polynomial in `g` pulls back to one in `f` ⇒ Hölder ⇒ BRIDGE. Methods: 3 reverse, 19 write the fake proof, 20 name the missing lemma (the pullback elimination lemma).

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C04.

## Log
- 2026-06-20 — created in 0-backlog from bucket C04.
