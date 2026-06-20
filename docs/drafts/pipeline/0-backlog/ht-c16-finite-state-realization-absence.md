# Finite-state realization absence — no finite algebraic state-space machine generates f

- **ID:** ht-c16-finite-state-realization-absence
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C16
- **Statement:** Generic `f ∈ HT` is not the output of a finite-dimensional algebraic state-space system with DA coefficients, hidden states, and inputs, unless elimination fails because the system smuggled in `f`-level data.

## Goal
Block a **finite hidden-state machine** generating `f`. Door: a control-theoretic disguise of a finite differential constraint; needs the elimination lemma made explicit.

## Door grade (hint)
**BRIDGE-likely.** State-elimination on a finite algebraic realization yields an input/output differential equation.

## Approach
Elimination test: eliminate the finite hidden states (differential elimination / characteristic set) from the realization to get an i/o differential polynomial in `f` ⇒ Hölder ⇒ BRIDGE. Name the elimination lemma precisely (the missing step). Methods: 4 change viewpoint, 17 change representation, 20 name the missing lemma.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C16; C17 (rewrite systems), C25 (operator rank).

## Log
- 2026-06-20 — created in 0-backlog from bucket C16.
