# Friable Dirichlet derivative at one

- **ID:** friable-dirichlet-derivative-at-one
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `friable-dirichlet-auxiliary.md` §5
- **Statement:** For a finite friable exponential Dirichlet auxiliary indexed by prime exponent vectors, the `T`-th derivative at `s=1` is `(-1)^T sum_m lambda_m (sum_p m_p log p)^T / n_m`.

## Goal
This banks the derivative identity at the arithmetic edge `s=1`. It does not formalize the auxiliary-space structure `A_{S,d}`, the multinomial expansion into log-monomials, the surjectivity lemma, or any Schanuel/algebraic-independence lower bound.

## Paper Proof
For a single term, write `n^{-s}=exp(-s log n)`. Repeated differentiation gives
`d^T/ds^T exp(-s log n) = (-log n)^T exp(-s log n)`. Evaluating at `s=1` gives
`(-1)^T (log n)^T / n`.

For a finite sum, derivatives pass through the finite sum term-by-term. If `n_m=prod_p p^{m_p}`, then unique factorization gives
`log n_m = sum_p m_p log p`. Substitution yields
`F^{(T)}(1)=(-1)^T sum_m lambda_m (sum_p m_p log p)^T / n_m`.

## Gates
- [x] 0 -> 1  in-progress: derivative-at-one identity extracted.
- [x] 1 -> 2  fully-proven: paper proof above, by repeated differentiation of finite exponential sums.
- [x] 2 -> 3  formalized: Lean theorem `iteratedDeriv_friableExponentDirichletExp_at_one` and supporting theorems in `formal/GaloisForLFunctions/RHTower/FriableAuxiliary.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the derivative identity in the friable auxiliary note.

## Log
- 2026-06-19 — Leaner split this exact derivative identity from `friable-dirichlet-auxiliary`. The parent card remains in `2-fully-proven` because the auxiliary-space construction, multinomial/log-monomial expansion, surjectivity, and Schanuel-bound layers are not fully Lean-formalized.
