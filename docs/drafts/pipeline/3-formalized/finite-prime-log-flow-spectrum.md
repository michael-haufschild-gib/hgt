# Finite prime-log flow spectrum

- **ID:** finite-prime-log-flow-spectrum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/constraint-not-flow-theorem.md` §1 and reused by `../2-fully-proven/archimedean-generator-axis-mode.md`
- **Statement:** A finite integer Fourier character on the prime torus has diagonal Kronecker-flow frequency `sum_p m_p log p`; the frequency is zero iff the character is trivial, and an axis mode has frequency `k log p`.

## Goal
This banks the exact finite algebraic core of the Source-B flow computation. It does not claim the infinite torus spectral theorem, Haar equidistribution, Hilbert-Polya scope, or any archimedean positivity statement.

## Paper Proof
Let `m : P ->_fin Z` be a finite prime-exponent vector. The diagonal flow sends the prime coordinate by
`x_p(t) = x_p(0) exp(-it log p)`. Therefore the character
`e_m(x) = prod_p x_p^{m_p}` is multiplied by
`exp(-it sum_p m_p log p)`, so its frequency is
`omega(m) = sum_p m_p log p`. For the axis vector `k delta_p`, this gives
`omega(k delta_p) = k log p`.

If `omega(m)=0`, then
`sum_p m_p log p = log(prod_{m_p>0} p^{m_p}) - log(prod_{m_p<0} p^{-m_p}) = 0`.
Exponentiating gives equality of two positive integers with prime factorizations
`prod_{m_p>0} p^{m_p}` and `prod_{m_p<0} p^{-m_p}`. Unique factorization forces every exponent to be zero, hence `m=0`. The converse is immediate. Thus every nontrivial finite character has nonzero frequency.

## Gates
- [x] 0 -> 1  in-progress: finite-character frequency statement extracted from the broader flow card.
- [x] 1 -> 2  fully-proven: paper proof above, using only the diagonal-flow character computation and unique factorization.
- [x] 2 -> 3  formalized: Lean theorems `primeLogFrequency_single`, `primeLogFrequency_eq_zero_iff`, `primeLogFrequency_ne_zero`, and `primeLogFrequency_single_ne_zero` in `formal/GaloisForLFunctions/KroneckerFlow.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the finite Source-B flow lemma in the HP/constraint note.

## Log
- 2026-06-19 — Leaner split this exact finite lemma from the broader `constraint-not-flow-theorem` and created the formalized card. The parent card remains in `2-fully-proven` because its infinite torus, orthogonality, DSS, and Connes/HP scope are not fully Lean-formalized.
