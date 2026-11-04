# Does the pole pay the prime 3?

- **ID:** swc-pole-pays-prime-three
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.8 follow-up; `swc-signed-certificate-below-log-four`
- **Statement:** On windows `[−c, c]`, `½ log 3 < c ≤ ½ log 3 + 1/40` (prime 3 acts and is collar-unpaid,
  `exists_prime_three_collar_unpaid`), decide which resource pays the prime-3 coupling — the pole, the
  trivial-zero Hankel squares, or the archimedean edge energy — and prove the answer.

## Goal
Band form below `log 4` (`zetaWindowPositive_iff_two_three_markov_hankel`), half-window `f` on `[−c, 0]`,
`M = archForm f`, `C, S` cosh/sinh half-moments, `m_* = leftMoment f (−½)`, `μ_k = leftMoment f σ_k`,
`s_n = (f⋆f)(−log n)`:
- odd: `4S² ≤ M + m_*² + Σ_k μ_k² + w₂s₂ + w₃s₃`;
- even: `m_*² + Σ_k μ_k² + w₂s₂ + w₃s₃ ≤ M + 4C²`.
Answer either with an exact payment mechanism for the prime-3 term or with an obstruction plus survivor.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
1. Numerics (scratch only): ground energies of both sectors, admissible `w₃`- and `w₂`-slices of
   `belowLogFourBandWeights c`, effect of the Hankel squares, location of extremals.
2. Structural facts about the prime-3 term on the entry windows (support on the collar sliver,
   mirror symmetry about `−½ log 3`), proved in Lean.
3. Conjecture loop on the payment law.

## Conjectures

## No-go closure (mandatory when falsified)

## Log
- 2026-11-04 — created in 1-in-progress
