# Counting holography (CTH) — programme card

- **ID:** cth
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0711/obstacles-summary.md §2.7, §2.10
- **Statement:** quantum numbers of boundary sources on arithmetic quotients of AdS: a count law (Born rule for open channels) is what separates true curves from fakes, and over ℤ it is the open door.

## Goal
Develop the field of §2.10: objects, tools, answers to its six questions, calibration on true curves,
fakes, throats, the genus-two graph and Farey counts. Lean folder
`formal/GaloisForLFunctions/CountingHolography/`, umbrella `CountingHolography.lean`, README there.

## Gates
- [x] 0 → 1  in-progress: questions and tools fixed by §2.10; attack per question below
- [ ] 1 → 2  every answered question has a paper proof
- [ ] 2 → 3  every answer formalized, module checked with `lake --old env lean`

## Questions and tools (status)

| Item | Content | Status |
|---|---|---|
| Rung | genus-two graph: count law at level one ⟺ `(q-2)² ≤ 16q`; at every level ⟺ `q ≤ 3` | open |
| Every genus | tower count law ⟺ unitary datum, every genus | open |
| Q2 | parallelogram law with delay covariance = partner law; positivity = damping | open |
| Q1 / door | RH ⟺ integer-probe form is the quadratic growth rate of a count | open |
| Q3 | integrality + sharp trivial zeros + first count law do not force the tower law | open |
| Q4 | boundary square ⟺ oscillating mode ⟺ CM lattice | open |
| Q5 | Hecke supplies conservation at every level, holds on fakes | open |
| Q6 / T5 | horocycle mean = totient-weighted count of cusp images; rate 3/4 = square-root Farey law | open |

## Approach
Count law = (quadratic, delay-covariant) + (count). The first half is the functional equation,
the second the sign. Calibrate every statement on curves (Manin), fakes (count `|𝒬|`), throats
(no FE), genus-two graph (FE, slow for `q ≥ 4`).

## Log
- 2026-11-07 — created
