# Approximate differential-complexity divergence — minimal model complexity → ∞

- **ID:** ht-c26-approx-complexity-divergence
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C26
- **Statement:** Fix a norm on a compact subdomain and bound the degree/order/height of differential polynomials over `K`. For generic `f ∈ HT`, the minimal complexity of a differential polynomial approximating `f` to tolerance `ε` tends to `∞` as `ε→0`, with no eventual bounded template.

## Goal
Give a **quantitative, monotone, falsifiable** form of HT: exact zero residual at fixed complexity is forbidden, and the approximate version diverges. Door: turns the (A) absence into a measurable curve — directly experiment-driven.

## Door grade (hint)
**BRIDGE-likely (quantitative refinement).** Provable lower bounds may follow from a quantitative Hölder/elimination estimate; primarily a numerics target.

## Approach
Define `c(ε)=min complexity achieving residual ≤ ε`; show no bounded template (else a limiting exact relation contradicts HT). mpmath: tabulate `c(ε)` for Γ-like and random `f`, look for divergence vs plateau. Methods: 11 run experiments, 13 monotone quantity, 14 weaken.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C26; C08 (Padé), C25 (operator rank).

## Log
- 2026-06-20 — created in 0-backlog from bucket C26.
