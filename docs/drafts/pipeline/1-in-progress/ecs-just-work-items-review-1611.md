# ECS just-work items of review 1611 (E-J1–E-J9)

- **ID:** ecs-just-work-1611
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper → Lean), one module per item
- **Source:** docs/reports/review-1611/route-ecs.md §4
- **Statement:** the nine just-work items of the ECS route report, each as unconditional Lean theorems about the critical state.

## Goal
Close the assembly-level gaps of the ECS route: the exact index law, higher critical states, the zero Parseval identity, the zero pairing of two profiles, the probe form of RH, mode expansions, the trivial-zero reading of the archimedean tail, model states, the wall seen from the left. None of them is RH; they give the finite-dimensional form of stage 2 and the tools of the later stages.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (per item)
- [ ] 2 → 3  formalized (per item)

## Items

| Item | Module (ECS/) | Status |
|---|---|---|
| E-J3 zero Parseval identity | Zeros/TheZeroParsevalIdentityOfTheState.lean | in progress |
| E-J5(a) RH ⇔ Weil ≥ 0 on real probes | — | queued |
| E-J1 exact index law | — | queued |
| E-J4 zero pairing of two profiles | — | queued |
| E-J2 higher critical states | — | queued |
| E-J7 archimedean tail as trivial-zero sum | — | queued |
| E-J6 mode expansions | — | queued |
| E-J9 wall seen from the left | — | queued |
| E-J8 model states | — | queued |

Other agents work on ECS in parallel: new modules only; the umbrella gets one import line per finished module.

## E-J3 paper proof
Let S(ε) = Σ_q LF(z_q)LF(−z_q)e^(εz_q²) (summable for ε > 0, criticalState_hasSum_zeroPairing_heated with G = F) and S(ε) → −aW₈ (criticalState_tendsto_zeroNorm). Split the copies into on-line (Re z = 0) and off-line. For Re z = 0: −z = z̄, LF(z̄) = conj LF(z) (F real), z² = −(Im z)², so the term is e^(−ε(Im z)²)|LF(z)|² ≥ 0, ≤ |LF(z)|², increasing to |LF(z)|² as ε ↓ 0.
(i) If the off-line part tends to L, the on-line part R(ε) (real) tends to M = −aW₈ − L, so M is real. For a finite set T of on-line copies, Σ_T|LF|² = lim Σ_T e^(−ε γ²)|LF|² ≤ lim R(ε) = M; hence summable with Σ ≤ M; and Σ|LF|² ≥ R(ε) → M. So Σ_on |LF|² + L = −aW₈.
(ii) If the on-line values are square-summable, dominated convergence (Tannery) gives R(ε) → Σ_on|LF|², so the off-line part tends to −aW₈ − Σ_on|LF|².
(iii) With finitely many off-line copies the off-line part is a finite sum and tends to Σ_off LF(z)LF(−z).

## Log
- 2026-11-16 — created; E-J3 started.
