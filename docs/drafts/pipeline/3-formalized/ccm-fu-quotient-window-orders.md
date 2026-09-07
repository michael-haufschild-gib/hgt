# CCM-FU: complete quotient-window orders after arbitrary processed states

- **ID:** CCM-FU-QUOTIENT-WINDOW-ORDERS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Result:** Every actual quotient window, and every selected subpool of it, admits a complete distinct prime order after any processed state. Every prefix energy is bounded by the initial, final, and one separating energy fixed by the source's transverse sign before choosing the order. No retained-sign or unproved arithmetic bound is assumed by the complete-window theorem.

## Exact source and window

Let `F_M(P,R)` be the literal retained divisor fibre and `E_M(P)` its complete
energy. The canonical pool is

`U(M,N,P)={p prime: p<M, p notin P, floor(M/p)=N, N+1<=p}`.

A selected subpool may be any subset U of this canonical pool. This permits
repeated partial-window interleavings; the theorem does not require consuming
the entire pool in one contiguous block.

Write `w_p` for the exact clipped square-root clock weight. The p-containing
field is

`v_p(R)=-sqrt(p)((1-w_p)F_N(P,R)+w_p F_(N+1)(P,R))`.

This is the actual copied field, including its sign and terminal phase.
Every pool prime is inactive at both smaller cutoffs, so processing any subset
L of the pool leaves both fields, and therefore every v_p, unchanged. A retained
label containing a pool prime vanishes at both smaller cutoffs. Equivalently,
two distinct pool primes cannot occur together in an active source coefficient:
`M<p(N+1)<=pq`.

## Exact signed marginal

Define the complete packet Gram kernel

`G(p,q)=sum_R v_p(R)v_q(R)`

on the actual ambient prime-label powerset. The exact insertion law gives

`E_M(P union (L union {q}))-E_M(P union L)
 =2 sum_R F_M(P,R)v_q(R)+2 sum_{p in L} G(p,q)`.

No overlap is dropped. To prove this, first use the exact prime-merger cross
identity. The q-containing partner is the unchanged packet v_q. The sum over
labels excluding q extends to all labels because v_q vanishes on labels
containing q. For labels disjoint from L, repeated insertion gives
`F_M(P union L,R)=F_M(P,R)+sum_L v_p(R)`. On the remaining labels v_q is zero,
so the same equality holds after multiplication by v_q. Finite sum exchange
then gives the displayed marginal.

## A source-fixed split into two classes

Set `A_R=F_N(P,R)` and `D_R=F_(N+1)(P,R)-A_R`. Define the transverse coordinate

`tau_p=sum_R (A_R+w_p D_R)D_R`.

The separating set is the explicit source function

`U_plus={p in U: tau_p>=0}`,

implemented by `mobiusDivisorQuotientPositivePart`. It is fixed independently
of the later order; the theorem does not introduce an unspecified peak subset.

For `H=sum A_R^2`, `C=sum A_R D_R`, and `Q=sum D_R^2`, Cauchy–Schwarz gives
`C^2<=HQ`. The exact identities are

`<A+tD,D>=C+tQ`,

`<A+tD,A+uD>=H+(t+u)C+tuQ`,

`Q<A+tD,A+uD>-<A+tD,D><A+uD,D>=HQ-C^2>=0`.

When the transverse coordinates have the same sign, their product is
nonnegative and the inner product is nonnegative. If Q=0, Cauchy–Schwarz forces
C=0 and the inner product is H>=0, so the degenerate case is included.
The reflected square-root factors of the actual packets have nonnegative
product. Thus G(p,q)>=0 within U_plus and within its complement. These Gram
entries remain unchanged after processing U_plus.

## Complete ordering with increasing marginals

For a real function f on subsets of a finite pool, assume inserting a fixed
unused element has a nondecreasing marginal as the processed subset grows.
There is a complete distinct order with every prefix value at most
`max(f(empty),f(full))`.

Prove this by strong induction on the pool. If a first insertion contracts f,
perform it and apply induction to the shifted problem. If none contracts,
every initial marginal is positive. The increasing-marginal property makes
all later marginals nonnegative, so the final endpoint bounds every subset.
This proves existence of an order; it does not assert that every order works.

The exact arithmetic marginal above has this property within either
transverse class because the added Gram terms are nonnegative. Order U_plus
first and its complement second, applying the theorem to the second block
from the actual state `P union U_plus`. Their packet Gram kernel is unchanged.
Concatenation is a complete distinct order of U, with every prefix energy at
most the three **predetermined** values

`max(E_M(P), E_M(P union U_plus), E_M(P union U))`.

This applies after arbitrary P, including states whose original retained
signs have changed. The final complete-window theorem takes only M,N,P as
inputs and has no unproved arithmetic premise.

## Remaining frontier

The three source-defined endpoint energies are not bounded by the original
diagonal here. They remain the arithmetic obligation for using these orders
inside a globally bounded growing schedule. In particular, the existing
late-prime capacity theorem still prevents consuming all required late mass
in a fixed number of uniformly budgeted blocks. Arbitrary subpools are
available for growing interleavings, but a successful global choice and its
endpoint estimates remain unproved. This theorem does not close SD1, RH, or
the all-cutoff two-prime ceiling.

## Lean and verification

- `RHTower.AffineFieldSubsetOrder`: three public theorems for increasing
  marginals, the affine Gram split, and concatenating two endpoint-bounded orders.
- `RHTower.MobiusDivisorQuotientWindowOrder`: five public source definitions
  and eight public theorems, including the exact marginal and
  `exists_mobiusDivisorQuotientSubwindowOrder` /
  `exists_mobiusDivisorQuotientWindowOrder` with the source-fixed separator.

Both scratch files and both exact leaves passed `lake env lean`. Only two new
required oleans were generated, and both leaves are wired once without full,
umbrella, or dependency rebuilds. All sixteen new public declarations were
axiom-audited once in a separate scratch file: only `propext`,
`Classical.choice`, and `Quot.sound`, with no added axioms or computational
certificates. No numerical experiment was run. The declaration index was
refreshed once. New-file whitespace, source-card links, added references,
both umbrella imports and scoped tracked whitespace checks passed.

Global formal lint reports eleven unwired modules elsewhere in the shared
worktree (`ThetaCuspEvenCompact*` and `PolynomialODEEvenCompact*`), alongside
132 existing large-file warnings. Neither new CCM-FU leaf is among those
errors. Those other modules were not changed by this work.
