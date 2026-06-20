# Operator-rank noncompression — the jet tower is in no finite-rank operator module

- **ID:** ht-c25-operator-rank-noncompression
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C25
- **Statement:** The derivative tower `(f^{(n)})` of generic `f ∈ HT` lies in no finite-rank module over rings of DA operators; Wronskian/Hankel/Krylov-type rank tests do not become eventually bounded for structural reasons.

## Goal
Block a **finite-dim linear/operator handle** containing the infinite jet tower — the broad operator-rank generalization of "not D-finite". Door: a linear-algebraic compression axis.

## Door grade (hint)
**BRIDGE-likely.** Eventual Wronskian/Hankel rank boundedness ⇒ a linear dependence among jets over the operator ring ⇒ a differential/algebraic relation ⇒ excluded.

## Approach
Elimination test: bounded Wronskian rank `⇒ ∃` linear relation `Σ a_i f^{(i)} = 0` with DA `a_i` ⇒ a differential polynomial ⇒ BRIDGE; Hankel bound ⇒ algebraic relation among jets (cf. C08). Methods: 12 find an invariant, 13 monotone quantity (rank), 17 change representation.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C25; C07 (recurrence), C08 (Padé/Hankel).

## Log
- 2026-06-20 — created in 0-backlog from bucket C25.
