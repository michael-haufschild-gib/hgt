# Finite Prolate-Channel Boundary Repairs Are RH Strength

- **ID:** finite-prolate-channel-boundary-rh-strength
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route normalization
- **Source:** `finite-rank-boundary-schur-index.md`,
  `finite-boundary-ideal-q0-rh-equivalence.md`,
  `finite-rank-counterterm-kernel-visibility.md`
- **Statement:** Any all-order finite-channel boundary repair whose channels are
  evaluations at finitely many exterior real points, including any fixed finite
  subset of the pole/trivial-zero `4N+1` prolate channels, remains RH-strength.
  The repair vanishes on the finite boundary ideal, and positivity on that ideal
  is already equivalent to RH.

## Setup

Let `Y` be the folded reciprocal nontrivial-zero support of the completed
Riemann `xi`, with positive folded multiplicities `M_y` and

`sum_y M_y |y| < infinity`.

Set

`Q_0[p]=sum_y M_y y p(y)^2`

for real polynomials `p`.

Let

`B={b_1,...,b_r} subset R`

be a finite boundary set disjoint from `Y`, and define the boundary evaluation
map

`L_B(p)=(p(b_1),...,p(b_r))`.

Let `C` be any real quadratic form on `R^r`, and define

`R_C[p]=Q_0[p]+C(L_B p)`.

For the prolate-channel route, the finite sets are of the form

`b_N=-(2N+1/2)^{-2}`

with finitely many selected `N` values: `N=0` is the pole image `-4`,
`N=1` is the first trivial-zero image `-4/25`, and `N>=2` are protector-tail
channels.

## Theorem

If

`R_C[p]>=0 for every real polynomial p`,

then RH holds.

If, in addition, `C` is positive semidefinite, then RH is equivalent to
positivity of `R_C` on all real polynomials.

## Proof

Let

`h(y)=prod_{j=1}^r (y-b_j)`.

For every real polynomial `q`, the polynomial `p=hq` satisfies `L_B(p)=0`.
Therefore the boundary term vanishes:

`C(L_B(hq))=0`.

Positivity of `R_C` gives

`0 <= R_C[hq] = Q_0[hq]`

for every real polynomial `q`.

Since `B` is disjoint from `Y`, the polynomial `h` has no zero on the reciprocal
support. By `finite-boundary-ideal-q0-rh-equivalence.md`, all-order positivity
of `Q_0[hq]` for every `q` is equivalent to RH. Hence positivity of the repaired
finite-channel form implies RH.

Conversely, if RH holds and `C>=0`, then `Q_0[p]>=0` for every real polynomial
`p`, and `C(L_B p)>=0`, so `R_C[p]>=0`.

## Consequence for the RH Route

The matrix Schur theorem identifies the finite boundary quotient at a fixed
degree. This theorem identifies what happens at all degrees for any fixed finite
set of exterior channels: the kernel ideal already has RH strength.

Thus a fixed finite prolate-channel repair is not a softer target. It either:

1. proves an RH-equivalent all-order kernel positivity statement; or
2. hides atoms only by using boundary data that see reciprocal atom evaluations,
   which must be source-built and audited separately.

The corrected semilocal route must therefore be full-channel/all-order, with a
source theorem controlling the degree and channel limits. A finite channel set,
including the scalar `N=1` first-trivial-zero channel, is only a height-graded
shadow.

## Theatre Test

For any proposed finite prolate-channel proof:

1. Which finite set `B` of channels is used?
2. Is `B` disjoint from the reciprocal nontrivial-zero support?
3. What happens on the ideal `prod_{b in B}(y-b) R[y]` where the boundary repair
   vanishes?
4. Is the proof deriving that ideal positivity from source data, or assuming an
   RH-equivalent all-order cone?

## Gates

- [x] 0 -> 1 in-progress: finite prolate-channel shortcut isolated.
- [x] 1 -> 2 fully-proven: boundary-ideal reduction proves RH-strength.
- [ ] 2 -> 3 formalized: optional specialization of finite-boundary ideal
  theorem plus finite evaluation kernel.

## Log

- 2026-06-24 -- Codex: created after the finite-rank boundary Schur index card
  to prevent a fixed finite prolate-channel matrix from being mistaken for a
  non-equivalent source selector.

## 2026-06-24 summable full-channel extension

`summable-exterior-boundary-measure-rh-strength.md` extends this fixed finite-channel guardrail to infinite exterior boundary supports with finite total variation. In particular, the summable full trivial-zero/prolate tail still cannot hide an off-line reciprocal atom when its support is disjoint from the nontrivial reciprocal divisor.

Thus passing from finitely many exterior channels to the full summable exterior measure does not by itself create a non-equivalent source selector. The semilocal route needs a source theorem beyond summable exterior boundary positivity.
