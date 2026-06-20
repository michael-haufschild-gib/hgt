# Perturbative HT density — small generic perturbations land in (and stay in) HT

- **ID:** ht-c23-perturbative-density
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C23
- **Statement:** Around any sufficiently regular function, arbitrarily small generic perturbations are HT; conversely, a generic small perturbation of an HT function remains HT.

## Goal
Establish **stability/instability of handles under perturbation**: exact algebraic-differential identities are fragile; HT is open under generic small noise. Door: a perturbative companion to the topological-largeness claim C22.

## Door grade (hint)
**Genuinely-new flavour.** Exact polynomial identities are non-generic; a tiny generic perturbation should destroy them without installing a new one.

## Approach
Show `{P(f)≡0}` has empty interior in the chosen norm (perturb one Taylor coefficient to break any fixed `P`); diagonalize over countably many `P`. Pair with mpmath experiments. Methods: 2 attack-as-false, 8 similar objects, 11 run experiments.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C23; C22 (topological), C24 (random).

## Log
- 2026-06-20 — created in 0-backlog from bucket C23.
