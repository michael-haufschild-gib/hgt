# Signed Window Criticality (SWC) — programme card

- **ID:** SWC
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0311/obstacles-summary.md §2.7 (signed arithmetic criticality theory
  of the window tower), §2.8 (the one question), §2.6.1
- **Statement:** the ground-state theory of Weil's form on symmetric windows with every sign kept:
  sector forms, signed conductances and their frustration loci, signed ground-state representations,
  pole capacities, Kron reduction of negative edges, stage passage, critical ground states.

## Goal
Answer the four questions of §2.7 and the one question of §2.8 by Lean theorems or labelled
no-gos with survivors. Folder `formal/GaloisForLFunctions/SignedWindowCriticality/`, umbrella
`SignedWindowCriticality.lean` (wired into `MainTheorems.lean`), README there. ACT, WTZ, GWZ, CSTW,
DZG, CWS, LST and the F1 cards belong to other agents: import, never edit.

## Numerical picture (research numerics, polynomial basis on `[−a, a]`)
| half-width `a` | `μ₊(W)` even | `μ₋(W)` odd | `λ₀(M)` Markov | frozen odd | `M` odd |
|---|---|---|---|---|---|
| 0.30 | 7.6e-3 | 0.223 | −1.12 | 0.223 | 0.230 |
| 0.40 | 1.8e-4 | 1.47e-2 | −1.54 | −0.078 | 0.030 |
| 0.50 | 9.4e-7 | 1.95e-4 | −1.99 | −0.322 | 0.0198 |
| 0.549 | 5.7e-8 | 1.54e-5 | −2.17 | −0.430 | 0.0152 |

- The Markov part `M = W − pole` turns indefinite at window length ≈ 0.22; its ground state is even
  and positive (Z-type).
- Sector ground states of `W` are positive on the open half-window; the `n`-th eigenfunction of a
  sector has `n` nodes; even and odd eigenvalues interlace; at criticality the ground state vanishes
  at the window edge.
- `M` odd and the frozen even form have ground states with a node (frustration).

## Gates
- [x] 0 → 1: questions fixed, corpus dictionary read (ACT, GWZ, CSTW, WTZ, DZG, CWS, RHTower Markov–pole).
- [ ] README first draft.
- [ ] Pillars in Lean (see README §8).

## Log
- 2026-11-03 — created.
