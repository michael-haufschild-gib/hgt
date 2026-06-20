# Algebraic addition-theorem absence — no binary group-law handle

- **ID:** ht-c02-addition-theorem-absence
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C02
- **Statement:** For generic `f ∈ HT_K`, no nonzero polynomial relation among finitely many jets of `f(x), f(y), f(x+y)` vanishes identically in two independent variables.

## Goal
Rule out a **binary functional handle** (algebraic addition theorem) that would compress `f` to values at fewer arguments. Door: a distinct functional-handle axis, not reachable from the one-variable `∂`-obstruction.

## Door grade (hint)
**BRIDGE-likely** (function-level, (A)-side). Classical addition theorems co-occur with finite algebraic/differential structure; the elimination should expose a forbidden one-variable relation.

## Approach
Elimination test: differentiate the putative addition relation in `x` and `y`, set `y→0`; if the two-variable relation collapses to a one-variable differential polynomial in `f`, it reduces to Hölder ⇒ BRIDGE. The genuinely-new case is one that survives the diagonal collapse. Methods: 1 split into subclaims, 3 reverse, 21 dependency chain.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C02; companion functional-handle cards C03, C05.
- `hypertranscendence-axis-synthesis.md` §1 (A-side).

## Log
- 2026-06-20 — created in 0-backlog from bucket C02.
