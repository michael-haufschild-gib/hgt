# Exclusion of the critical state (ECS)

- **ID:** ecs
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** docs/reports/review-1511/obstacles-summary.md §2.18 ("the most likely route to a proof, as a research programme")
- **Statement:** make every exact property of the critical half-line state a Lean theorem (stages 1–4: probe kernel, zero side, (★), continuation, sign/decay laws, index law) and attack stage 5 (no state for the zeros of ζ).

## Goal
README: `formal/GaloisForLFunctions/ExclusionOfTheCriticalState/README.md` (Q1–Q9). Lean in
`formal/GaloisForLFunctions/ExclusionOfTheCriticalState/`, umbrella `ExclusionOfTheCriticalState.lean`.

## Gates
- [x] 0 → 1 in-progress: README draft, questions Q1–Q9
- [ ] 1 → 2 fully-proven: per conjecture below
- [ ] 2 → 3 formalized: per module

## Approach
Order: Q1 probe calculus (pole, prime, Gamma parts on `e_p`, Poisson integral of Re ψ) → probe kernel;
state's probe identity in prime coordinates; Q6 finite index law; Q2/Q3 zero side on the domain → (★);
Q5 sign law via Landau; Q4 decay law (divergent half). Stage 5 entry points: wall, collar, charges, difference equation.

## Conjecture ledger

## Log
- 2026-11-16 — created; README draft written.
