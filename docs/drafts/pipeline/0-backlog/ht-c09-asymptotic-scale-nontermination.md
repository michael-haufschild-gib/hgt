# Asymptotic-scale nontermination — no finite asymptotic code generates the tail

- **ID:** ht-c09-asymptotic-scale-nontermination
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C09
- **Statement:** If generic `f ∈ HT` admits an asymptotic expansion in a chosen DA scale, no finite initial segment determines the tail by algebraic-differential rules internal to that scale.

## Goal
Block a **finite asymptotic code** recursively generating the remaining expansion. Door: collapse can hide in tails rather than in derivatives — an asymptotic-representation handle.

## Door grade (hint)
**BRIDGE-likely.** A finite tail-recursion in a DA scale is a disguised finite differential constraint.

## Approach
Elimination test: a recursion law among asymptotic coefficients within a DA scale translates (via the scale's DA generators) to a differential polynomial in `f` ⇒ BRIDGE. Methods: 7 strip to essentials, 13 monotone quantity (truncation error), 17 change representation.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C09; C29 (resurgence — beyond ordinary scales).

## Log
- 2026-06-20 — created in 0-backlog from bucket C09.
