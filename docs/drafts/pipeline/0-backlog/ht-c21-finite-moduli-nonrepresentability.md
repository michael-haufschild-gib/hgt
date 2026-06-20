# Finite moduli nonrepresentability — no finite-dim moduli space parameterizes generic HT

- **ID:** ht-c21-finite-moduli-nonrepresentability
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C21
- **Statement:** Generic HT functions cannot be parameterized, even up to natural DA transformations, by points of any finite-dimensional algebraic or differentially algebraic moduli space.

## Goal
Block a **finite parameter list** classifying the object — a global compression at the level of classification rather than equation-solving. Door: the moduli-side analogue of "infinite differential transcendence degree" (note §3).

## Door grade (hint)
**BRIDGE-likely / structural.** A finite-dim DA moduli representation would bound the differential transcendence degree, contradicting `difftrdeg = ∞`.

## Approach
Elimination test: a finite-dim parameterization gives a finite generating set for `K⟨f⟩` over `K` ⇒ bounded differential transcendence degree ⇒ contradiction (note §3). Methods: 7 strip to essentials, 17 change representation, 21 dependency chain.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C21; C18/C19 (structural classification).

## Log
- 2026-06-20 — created in 0-backlog from bucket C21.
