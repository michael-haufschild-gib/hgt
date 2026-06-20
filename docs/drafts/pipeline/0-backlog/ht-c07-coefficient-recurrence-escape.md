# Coefficient-recurrence escape — no finite-width algebraic recurrence on Taylor coefficients

- **ID:** ht-c07-coefficient-recurrence-escape
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C07
- **Statement:** For generic analytic `f=Σ a_n (x-a)^n ∈ HT`, the coefficients `(a_n)` satisfy no finite-width algebraic recurrence `Q(n,a_n,…,a_{n+r})=0` (including nonlinear) over the base constants.

## Goal
Block a **finite recurrence grammar** for the Taylor coefficients — strictly beyond the linear holonomic (D-finite) case. Door: a coefficient-side handle, complementary to the analytic-side one.

## Door grade (hint)
**BRIDGE-likely (linear case) / possibly genuinely new (nonlinear case).** Linear bounded-width recurrence ⇔ D-finite ⇒ excluded by HT (synthesis §1). Nonlinear bounded-window recurrences are not obviously equivalent to a finite differential equation — that gap may be real.

## Approach
Elimination test: a linear width-`r` recurrence is equivalent to a holonomic ODE ⇒ excluded. For nonlinear `Q`, ask whether the generating-function translation yields a differential polynomial in `f`; if not provable, downgrade to a genuine open (B)-flavour sub-question. Methods: 9 test small cases, 17 change representation, 18 right theorem.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C07; C25 (operator-rank), C08 (Padé).

## Log
- 2026-06-20 — created in 0-backlog from bucket C07.
