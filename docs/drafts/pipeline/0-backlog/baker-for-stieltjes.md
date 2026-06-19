# A Baker for the Stieltjes constants

- **ID:** baker-for-stieltjes
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Priority:** FUTURE
- **Source:** ../../door/G2-multi-q-siegel-shidlovsky.md, ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status rows #18, #19
- **Statement:** A transcendence / independence lower bound for the Stieltjes constants `γ_n` (the
  Laurent coefficients of `ζ` at `s=1`) — the rung just above Baker's solved edge `L(1,χ)`.

## Goal
The Stieltjes block is the genuinely-new, no-motive part of G2/DSS: `ℚ({P_k}) = ℚ(π, {ζ(odd)},
{γ_n})`, and the `{γ_n}` are conjecturally not periods, so they sit beyond the Grothendieck period
conjecture. A transcendence result here is the concrete `s=1`-Laurent / archimedean attack on the DSS
open core. Source-pure: the `γ_n` are prime/continuation data, not the zeros.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door sketch (the archimedean seam,
  `ξ = Γ-factor × ζ`)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Aim a Nesterenko-type multiplicity estimate at the `s=1` Laurent data (where the `γ_n` live), not the
integer `ζ`-values. Start with a single concrete sub-target (e.g. irrationality of `γ_1`) before the
joint-independence statement.

## Log
- 2026-06-19 — created in 0-backlog
