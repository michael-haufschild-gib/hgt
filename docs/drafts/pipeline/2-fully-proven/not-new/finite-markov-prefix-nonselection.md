# Finite Markov Prefixes Do Not Select Stieltjes Positivity

- **ID:** finite-markov-prefix-nonselection
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / seam-log source-gate guardrail
- **Source:** `seam-log-markov-pick-rh-equivalence.md`,
  `seam-log-hankel-rh-equivalence.md`,
  `finite-linear-probe-rh-nonselection.md`,
  `rh-landscape-proof-gate.md`
- **Statement:** Any finite prefix of a shifted moment sequence can be preserved
  while a later Hankel square test is forced to fail. Therefore finite
  Markov/Pick/Hankel checks cannot certify the seam-log Stieltjes target.

## Setup

Let `(m_k)_{k>=0}` be a real sequence. The Stieltjes square-test condition is

`sum_{i,j=0}^d c_i c_j m_{i+j} >= 0`

for every degree `d` and every real vector `(c_0,...,c_d)`. Equivalently, every
finite Hankel block

`[m_{i+j}]_{0<=i,j<=d}`

is positive semidefinite.

In the seam-log route, `m_k=T_{k+1}^src`, and this all-degree condition is the
Markov/Stieltjes target equivalent to RH.

## Theorem

Fix `N>=0` and real numbers `a_0,...,a_N` with `a_0>0`. There is a real
continuation `(b_k)_{k>=0}` such that

`b_k=a_k` for `0<=k<=N`,

but `(b_k)` is not a Stieltjes moment sequence.

Moreover, the failure can be placed arbitrarily far beyond the prefix: for any
`n>N`, the continuation can be chosen so that the square test for

`q(y)=1-2y^n`

is negative.

## Proof

Choose any `n>N`. Define the continuation by preserving the prefix and setting

`b_n = a_0`,

`b_{2n}=a_0/4`,

with all other not-yet-specified entries assigned arbitrarily, for example
`a_0`.

This is consistent because `n>N` and `2n>N`, so neither value lies in the
prescribed prefix.

Evaluate the Hankel square test on the polynomial

`q(y)=1-2y^n`.

The value is

`b_0 - 4b_n + 4b_{2n}`.

Since `b_0=a_0`, `b_n=a_0`, and `b_{2n}=a_0/4`, this equals

`a_0 - 4a_0 + a_0 = -2a_0 < 0`.

Thus the continuation fails a finite square test and cannot be a Stieltjes
moment sequence.

Because `n` was arbitrary above `N`, the first failed test can be delayed past
any prescribed finite prefix.

If the prescribed prefix has positive entries, the displayed witness can be
chosen with positive entries at the two new witness indices as well. The failure
is not caused by a negative coefficient; it is caused by a later square-test
inequality.

## Positive Continuations Can Share The Same Prefix

If the prefix `a_0,...,a_N` already comes from a positive measure on `R_+`, then
there is also a positive Stieltjes continuation preserving it: take any such
representing measure and continue by its full moment sequence.

Thus the same finite prefix can be compatible with both:

1. a positive Markov/Stieltjes continuation;
2. a continuation that fails a later Hankel square test.

The prefix itself cannot decide which all-order branch has been chosen.

## Consequence For The Seam-Log Markov Target

`seam-log-markov-pick-rh-equivalence.md` identifies the RH target as the
all-order Markov/Stieltjes property of

`G_src(x)=sum_{k>=0} T_{k+1}^src x^k`.

This theorem says that no finite list of coefficients

`T_1^src,...,T_M^src`

and no finite list of Hankel minors using only those coefficients can certify
that target. A later square test can still fail while the entire finite prefix
is held fixed.

Therefore finite Markov/Pick interpolation, finite Padé or continued-fraction
data, finite Hankel positivity, and finite numerical Cholesky checks are only
calibration. They are not a source proof of RH.

## Route Impact

This theorem does not prove RH. It sharpens the proof obligation:

`source data => all-order Stieltjes positivity`.

The word "all-order" is load-bearing. It cannot be replaced by a growing
collection of finite certificates unless the proof supplies an independent
compactness, determinacy, or source-rigidity theorem that controls every later
square test.

## Gates

- [x] 0 -> 1 in-progress: finite Markov-prefix loophole isolated.
- [x] 1 -> 2 fully-proven: arbitrary-late negative square test constructed.
- [ ] 2 -> 3 formalized: finite sequence extension and polynomial-square
  calculation.

## Log

- 2026-06-24 -- Codex: created to make the seam-log all-order burden explicit
  in moment-prefix language.
