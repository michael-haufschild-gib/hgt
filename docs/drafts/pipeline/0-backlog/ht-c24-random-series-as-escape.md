# Random-series almost-sure escape — random analytic functions are a.s. HT and handle-free

- **ID:** ht-c24-random-series-as-escape
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C24
- **Statement:** A random analytic function with i.i.d. continuous coefficients is HT almost surely and, more strongly, a.s. avoids every finite symbolic handle from any prechosen countable menu (difference, recurrence, transform, algebraic-functional).

## Goal
Establish **probability-one escape** from all finite handles — the measure-theoretic form of largeness. Door: independent, experiment-friendly evidence stream for "constraint, not flow".

## Door grade (hint)
**Genuinely-new flavour (measure-theoretic).** A nonzero polynomial identity cuts a measure-zero condition on random coefficients; countable menu ⇒ a.s. avoidance.

## Approach
For each fixed `P`, `{coeffs : P(f)≡0}` is a positive-codimension (measure-zero) analytic condition on the coefficient vector; countable union stays null ⇒ a.s. HT. Pin convergence + continuity hypotheses. Methods: 8 similar objects, 11 run experiments, 17 change representation.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C24; C22/C23 (topological/perturbative largeness).

## Log
- 2026-06-20 — created in 0-backlog from bucket C24.
