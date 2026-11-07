# Review-0711 §2.1 Flow, near-line, continuation, orbit (A15–A24, A34)

- **ID:** r0711-flow-orbit
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), per task
- **Source:** docs/reports/review-0711/obstacles-summary.md §2.1 "Flow, near-line, continuation, orbit"
- **Statement:** complete and unconditional Lean solutions of A15–A24, A34, easiest first.

## Rules
No computations (A16 numerics and certified scans excluded). Corpus search first. `lake --old env lean` per module, foreground, one at a time. MMD cubic files belong to the A25–A33 session; CACT files to the A9–A14 session.

## Status
| # | Task | Status | Lean |
|---|---|---|---|
| A15 | RH ⇔ `Ψ` locally bounded | in progress | `CanonicalSystemOfTheWindowTower/ThePotentialIsLocallyBoundedIffRH.lean` |
| A16 | numerical `r,m,q` | excluded: computation | — |
| A17 | Selberg `O(T)` depth density, inner-field form | next | `ArithmeticInnerFunctionTheory/` |
| A18 | twisted second moments past `21/50` | open | |
| A19 | heat horizon toward method floor | open | |
| A20 | Jensen rung toward saddle scale | open | |
| A21 | census items, log two-point Chowla, runs past five | open | |
| A22 | VK `ζ(1+it)` bound into first-return bracket | open | |
| A23 | resonator mean of `|ζ(s+iτ)|²` on Bohr sets | open | |
| A24 | scans of `S_S` (computation), brackets `S*(a,b)` | open | |
| A34 | integrate [S] modules (PTT/TAPO/AAD; MMD cubic left to its owner) | open | |

## A15 — paper proof
Fix a precontact base `b`. `canonicalPotential_sub_eq`: `Ψ(y)−Ψ(x) = L(y)−L(x)+∫_x^y sinh 2L`, `L = artanh r` continuous on the precontact set.
- (⇒) Under RH the precontact set is `(0,∞)`; on `[b,c]` both `L` and `sinh 2L` are continuous, so `Ψ` is bounded.
- (⇐) Off RH let `a*` be the contact. If `|Ψ| ≤ M` on `[b,a*)`, then `|L| ≤ |L(b)| + 2M` there: if `L(y) > θ := max(L(b),0)+2M`, take the last `x ≤ y` with `L(x) ≤ max(L(b),0)`; on `(x,y]` `L > 0`, so `sinh 2L > 0` and `L(y)−L(x) ≤ Ψ(y)−Ψ(x) ≤ 2M`, contradiction; symmetric below. Then `m = cosh 2L` is bounded, `(log K)′ = 2m` keeps `K(i,i)` bounded below `a*`, contradicting `K(i,i) → ∞` at contact.

## Log
- 2026-11-07 — created; A17 found reducible to `eventually_offLineMoment_le_montgomeryTaylor` (`Σ m(β−½) ≤ 0.066 V`) plus `bounded_innerField_iff_depthDensity`.
