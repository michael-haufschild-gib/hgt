# ECS missed connections of review 1611 (E-M1–E-M9)

- **ID:** ecs-missed-connections-1611
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper → Lean), goal loop
- **Source:** docs/reports/review-1611/route-ecs.md §8
- **Statement:** formalize each corpus connection E-M1–E-M9 of the ECS route as unconditional Lean theorems about the critical state, with corollaries.

## Goal
Each E-M item names corpus results ECS does not import. The task is the theorem the connection gives, not a re-export. Order: easiest first.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (per item)
- [ ] 2 → 3  formalized (per item)

## Items

| Item | Target theorem | Module (ECS/) | Status |
|---|---|---|---|
| E-M2 | RH ⇔ Pick matrices (D(p)+D(q))/(p+q) PSD on any bounded-uniqueness set of real probe nodes (intervals, integers ≥ 5) | Pick/RealProbeNodesDecideTheRiemannHypothesis.lean | in progress |
| E-M3 | half-line one-bound-state law: RH ⇔ arch − prime ≥ 0 on the charge hyperplane of H; off RH it is negative there and ≥ −(a − γ)W₈ | — | queued |
| E-M4 | collar coercivity of the bare form; consequences for the weak equation on collar tests (E-Q4) | — | queued |
| E-M5 | archimedean wall tail in trivial-zero moments; Hankel sign | — | queued |
| E-M1 | probe index law: negative index of the probe kernel = #right zeros (Krein–Langer on real nodes); corollaries | — | queued |
| E-M7 | thick-lag receiver for the state (E-Q5) | — | queued |
| E-M9 | finite mode sets of the state are incomplete | — | queued |
| E-M6 | model table: Beurling Λ ≥ 0 model, FE rigidity, in ECS form | — | queued |
| E-M8 | function-field calibration (E-Q3) | — | queued |

Peers: the E-J loop (card ecs-just-work-items-review-1611.md) owns E-J1–E-J9; E-M2 ⊂ E-J5(a), E-M1 ⊂ E-J1, E-M5 = E-J7. New modules only; one import line each in the ECS umbrella.

## Paper proofs

### E-M2
Let S ⊆ (½, ∞) be a bounded-uniqueness set on Re w > ½ (an accumulation point in (½, ∞), or a Blaschke-divergent sequence → ∞, e.g. the integers ≥ 5). If the real Pick matrices of K(p,q) = B(e_p, e_q) = (D(p)+D(q))/(p+q) are PSD on S, then K is a PSD kernel on S (real symmetric), and Carathéodory–Pick gives G holomorphic on Re > 0 with Re G ≥ 0 and G = D on S. Cayley transforms c(G), c(D) = (·−1)/(·+1) are bounded by 1 on Re > ½ (Re D > 0 there unconditionally), and agree on S; so c(G) = c(D) and G = D on Re > ½. Then K = Carathéodory kernel of G on Re > ½, PSD, and RH follows from riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel. Converse: restriction.

## Log
- 2026-11-16 — created; E-M2 started.
