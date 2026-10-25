# What forces the actual arithmetic source to be blind to off-line zeros?

- **ID:** forcing-blindness-loop-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** docs/reports/review-2510/hard-obstacles-summary.md §3–4; AOG README §8
- **Statement:** Identify the arithmetic datum that forces blindness: prove which data provably
  cannot force it (with a sharp countermodel and a positive survivor) and which data do force
  it in which models.

## Goal
Narrow the forcing law to an explicit datum. Every unconditional positivity theorem in the corpus
is positivity on a blind carrier; RH is the statement that the actual source is blind. A forcing
law must be selective (fail on every battery model) and must not be a function of any datum that
a countermodel shares with `ζ`.

## Gates
- [x] 0 → 1  in-progress: question fixed, corpus searched, battery and engines catalogued
- [ ] 1 → 2  fully-proven: a forcing statement (not a blindness statement) with complete proof
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Selector ledger: for each candidate datum `D` decide (theorem) whether some countermodel shares
`D` with `ζ` and has an off-line zero. Data that survive are the only places a forcing law can
live. Each closed datum must leave a positive survivor naming what the forcing law has to read
instead.

| Datum | Status | Witness / survivor |
|---|---|---|
| Positive prime measure + integer-count regularity at any precision | CLOSED (contribution 1) | over-regular continuous system, `N(x) = ρx + C + x^{−a}(A₀ + A₁ log x)`; survivor: discreteness / lattice structure of the integers |

## Conjecture ledger
| # | Conjecture | Outcome | Lean |
|---|---|---|---|
| 1 | Integer-count regularity beyond `⌊x⌋` coexists with an off-line zero | PROVED | `RHTower/BeurlingOverRegularIntegersOffLineZeros` |

## Log
- 2026-10-25 — created in 1-in-progress
