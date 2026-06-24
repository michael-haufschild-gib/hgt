# Fixed-Rank Hankel Tests Do Not Imply Stieltjes Positivity

- **ID:** fixed-rank-hankel-tests-do-not-imply-stieltjes
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / positivity-transfer guardrail
- **Source:** `all-order-log-convexity-does-not-imply-stieltjes.md`;
  `finite-markov-prefix-nonselection.md`;
  `seam-log-markov-pick-rh-equivalence.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** For every fixed rank `r`, there is a strictly positive
  sequence whose shifted Hankel blocks of size at most `r` are positive
  definite at every shift, while a block of size `r+1` is indefinite. Thus a
  source proof cannot replace the full Stieltjes cone by any fixed-rank
  family of all-order Hankel tests.

## Setup

For a real sequence `(m_n)_{n>=0}`, define the shifted Hankel block

`H_{N,k}(m) = [m_{N+i+j}]_{0<=i,j<k}`.

The Stieltjes square-test condition requires positivity of such blocks at all
sizes, and also the corresponding one-step shifted family in the usual
source-forgotten Stieltjes formulation. In the seam-log RH route, the relevant
point is that no fixed block size can replace the full family of polynomial
square tests.

## Theorem

Fix `r>=1`. There exists a strictly positive real sequence `(m_n)_{n>=0}` such
that:

1. `H_{N,k}(m)` is positive definite for every `N>=0` and every `1<=k<=r`;
2. `H_{0,r+1}(m)` is not positive semidefinite.

Therefore all-order positivity of every shifted Hankel block up to a fixed size
`r` does not imply Stieltjes positivity.

## Proof

Choose distinct real numbers

`1 < x_1 < x_2 < ... < x_r`,

and set `y=1`. Let

`v_k(t)=(1,t,...,t^(k-1)) in R^k`.

For `1<=k<=r`, define

`A_k = sum_{j=1}^r v_k(x_j) v_k(x_j)^T`.

Because the `k x r` Vandermonde matrix with columns `v_k(x_j)` has rank `k`,
the matrix `A_k` is positive definite.

Choose `epsilon>0` so small that, for every `1<=k<=r`,

`A_k - epsilon v_k(y) v_k(y)^T`

is positive definite, and also `epsilon<r`.

Define

`m_n = sum_{j=1}^r x_j^n - epsilon y^n`.

Since `y=1` and each `x_j>1`, we have

`m_n >= r - epsilon > 0`

for every `n>=0`.

For each shift `N` and size `k<=r`,

`H_{N,k}(m)
 = sum_{j=1}^r x_j^N v_k(x_j)v_k(x_j)^T
   - epsilon y^N v_k(y)v_k(y)^T`.

Since `x_j^N >= 1 = y^N`, this gives the Loewner lower bound

`H_{N,k}(m) >= A_k - epsilon v_k(y)v_k(y)^T`.

By the choice of `epsilon`, the right side is positive definite. Hence every
`H_{N,k}(m)` with `k<=r` is positive definite.

Now examine `H_{0,r+1}(m)`. Let

`q(t)=prod_{j=1}^r (t-x_j)`.

This polynomial has degree `r`, so write it as

`q(t)=sum_{i=0}^r c_i t^i`.

Let `c=(c_0,...,c_r)`. Then

`c . v_{r+1}(x_j)=q(x_j)=0`

for every `j`, while

`c . v_{r+1}(y)=q(y) != 0`

because `y=1` is distinct from every `x_j`. Therefore

`c^T H_{0,r+1}(m) c
 = -epsilon q(y)^2 < 0`.

Thus `H_{0,r+1}(m)` is not positive semidefinite.

## Consequence For The Seam-Log Route

The previous Turan card handled the case `r=2` for adjacent tests. This theorem
shows that the issue is structural:

fixed-rank all-order Hankel testing is not the Stieltjes cone.

For the canonical seam-log tower, proving every shifted block of size at most
`r` is positive, for any fixed `r`, would still leave a possible failure at
size `r+1`. A proof of RH through the Markov/Stieltjes route must therefore
control arbitrary-degree polynomial square tests, or prove a source theorem
that upgrades a fixed-rank hierarchy to the full cone.

## Theatre Test

For any source proof that reports fixed-rank Hankel control:

1. What is the largest block size actually controlled?
2. Is the bound uniform in the shift only, or also in the block size?
3. Where is the theorem that prevents the negative-atom construction above at
   the next block size?
4. If no such theorem is supplied, the proof has not reached the RH-strength
   Stieltjes target.

## Source Boundary

This theorem is a finite-rank moment-cone counterexample. It proves no
positivity for zeta and no zero localization. Its role is to prevent an
all-order but fixed-rank positivity transfer from being promoted to the
source-built Stieltjes theorem.

## Gates

- [x] 0 -> 1 in-progress: fixed-rank all-order positivity loophole isolated.
- [x] 1 -> 2 fully-proven: signed-atomic construction proves positivity up to
  rank `r` and failure at rank `r+1`.
- [ ] 2 -> 3 formalized: finite Vandermonde rank plus rank-one perturbation
  argument.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation. The card
  upgrades the Turan/log-convex warning from adjacent `2 x 2` tests to every
  fixed-rank all-shift Hankel test.
