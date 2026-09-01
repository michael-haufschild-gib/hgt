# PW absolutely admissible unbounded matrix endpoint tomography

- **ID:** PW-AAUPM
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Every symmetric pairwise-positive countable PW matrix whose literal endpoint series is absolutely summable at the largest physical node is zero if dark at every physical node; no uniform matrix bound is needed.

## Goal

Kill the unbounded-but-absolutely-admissible survivor in
`PW endpoint darkness → response uniqueness → source balance → Borel partner balance → shared Ward endpoint → RH`.

## Gates

- [x] 0 → 1: corpus and literature searches found only bounded PW matrix tomography; exact rescaling attack fixed
- [ ] 1 → 2: dependency-closed paper proof
- [ ] 2 → 3: Lean theorem, targeted build, axiom audit, lint

## Approach

Let `q_j = exp (-(j+1))` and `a_n = ∑_{i=0}^n K(i,n-i)`. Absolute convergence at `q_0` makes `a_n q_0^n` summable, hence bounded. Since `q_{j+1}=q_0 q_j`, darkness at shifted physical nodes becomes bounded power-series darkness for coefficients `a_n q_0^n`; existing corpus uniqueness forces every `a_n=0`. Strong induction on even antidiagonals plus pairwise positivity then forces every row of `K` to vanish.

## Failure / survivor

- If rescaling fails, retain bounded theorem only.
- If proved, survivors must be indefinite, non-absolutely summable/singular, or leave pointwise quadratic endpoint energy.

## Audit

- Corpus: `scripts/formal_tools.py research` found bounded pairwise-positive theorem only; no unbounded absolute-admissibility theorem.
- Literature through 2026-08: searches found no PW endpoint-tomography or countable-kernel analogue; classical power-series uniqueness is only an ingredient.

## Log

- 2026-09-01 — conjecture frozen from PW corpus proof graph.
