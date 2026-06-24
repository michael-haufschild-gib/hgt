# All-Order Log-Convexity Does Not Imply Stieltjes Positivity

- **ID:** all-order-log-convexity-does-not-imply-stieltjes
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / positivity-transfer guardrail
- **Source:** `seam-log-markov-pick-rh-equivalence.md`;
  `seam-log-hankel-rh-equivalence.md`;
  `axis-positivity-does-not-imply-hankel-positivity.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** Positivity of every adjacent `2 x 2` Hankel minor
  (log-convexity / Turan inequalities) does not imply Stieltjes moment
  positivity. A source proof for the seam-log tower must control the full
  Hankel cone, not only all adjacent square tests.

## Setup

A positive sequence `(m_n)_{n>=0}` is log-convex if

`m_n m_{n+2} >= m_{n+1}^2`

for every `n>=0`.

Every Stieltjes moment sequence is log-convex, because each adjacent `2 x 2`
Hankel minor is positive semidefinite. The converse is false, even when
log-convexity holds for every `n`.

## Theorem

There is a strictly positive sequence `(m_n)_{n>=0}` such that:

1. `m_n m_{n+2} >= m_{n+1}^2` for every `n>=0`;
2. the `3 x 3` Hankel matrix `[m_{i+j}]_{0<=i,j<=2}` is not positive
   semidefinite.

Therefore all-order log-convexity is insufficient for Stieltjes positivity.

## Proof

Define

`m_0=1`,

`m_1=1`,

and, for `n>=2`,

`m_n=2(5/2)^(n-2)`.

Thus

`m_2=2`, `m_3=5`, `m_4=25/2`.

Log-convexity holds:

- for `n=0`, `m_0 m_2 - m_1^2 = 2-1 = 1`;
- for `n=1`, `m_1 m_3 - m_2^2 = 5-4 = 1`;
- for `n>=2`, the tail is geometric with ratio `5/2`, so
  `m_n m_{n+2} = m_{n+1}^2`.

Now consider the degree-two Hankel matrix

```text
[m_0 m_1 m_2]   [1 1 2]
[m_1 m_2 m_3] = [1 2 5]
[m_2 m_3 m_4]   [2 5 25/2].
```

Its determinant is

`det = -1/2`.

Hence this Hankel matrix is not positive semidefinite. A Stieltjes moment
sequence must have every Hankel matrix positive semidefinite, so `(m_n)` is not
a Stieltjes moment sequence.

## Consequence For The Seam-Log Route

The seam-log Markov target requires the full square-test cone:

`sum_{i,j=0}^d c_i c_j T_{i+j+1}^src >= 0`

for every degree `d` and every real vector `(c_0,...,c_d)`.

All adjacent Turan inequalities for the source coefficients,

`T_{n+1}^src T_{n+3}^src >= (T_{n+2}^src)^2`,

would still be too weak. They certify only adjacent `2 x 2` minors, while RH
requires every Hankel block and every polynomial square test.

Thus a proposed positivity transfer from Euler/Gamma/functional-equation source
data cannot stop at:

1. coefficient positivity;
2. complete monotonicity;
3. all adjacent log-convexity / Turan inequalities;
4. any other fixed-rank minor family that does not imply the full Hankel cone.

The proof must reach Stieltjes/Markov positivity itself, or provide an
independent source theorem that implies it.

## Theatre Test

For any source proof claiming a positivity transfer:

1. Which Hankel minors or square tests are actually controlled?
2. Does the proof control arbitrary polynomial squares, or only adjacent
   two-term tests?
3. If only log-convexity/Turan inequalities are proved, where is the theorem
   that upgrades them to the full Hankel cone?
4. If no upgrade is supplied, the proof has not reached the RH-strength
   positivity target.

## Source Boundary

This is an elementary counterexample. It proves no positivity for zeta and no
zero localization. Its role is to prevent an all-order but low-rank positivity
shadow from being mistaken for the source-built Stieltjes theorem.

## Gates

- [x] 0 -> 1 in-progress: weak all-order positivity transfer isolated.
- [x] 1 -> 2 fully-proven: explicit positive log-convex sequence with negative
  `3 x 3` Hankel determinant.
- [ ] 2 -> 3 formalized: finite determinant and geometric-tail
  log-convexity calculation.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after the
  `positivity-transfer` entropy selection. The card kills the route that tries
  to replace full seam-log Stieltjes positivity by all adjacent Turan
  inequalities.

## 2026-06-24 fixed-rank all-shift tests are insufficient

`fixed-rank-hankel-tests-do-not-imply-stieltjes.md` strengthens this guardrail. For every fixed size `r`, there is a strictly positive sequence whose shifted Hankel blocks `H_{N,k}` are positive definite for every shift `N` and every `k<=r`, while `H_{0,r+1}` is not positive semidefinite.

Thus the obstruction is not limited to adjacent Turan inequalities. Any proof that controls only a bounded block size, even at every shift, still has not reached the Stieltjes square-test cone.
