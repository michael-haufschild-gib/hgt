# Actual Möbius–divisor source diagonal dominance

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] candidate; unproved
- **Target:** an independent arithmetic inequality strong enough for RH.

## Frozen statement

Let `D(q)=log(q!)-sum_(n<=q)tau(n)+2 gamma q`, and

`K_d(M)=sum_(k=d)^(M-1) (sqrt(k+1)-sqrt(k)) D(floor(k/d))`.

**SD1:** for every integer M>=1,

`(sum_(d<=M) mu(d)K_d(M))^2 <= sum_(d<=M) mu(d)^2 K_d(M)^2`.

This is a source-specific proposal, not a statement about arbitrary square-root-bounded D.
Earlier finite controls provide motivation: the literal complete source had much smaller mean
square than its independently signed channels. Those observations do not imply SD1 pointwise.
The statement is classified as a bridge because the desired cancellation estimate determines it.
No novelty or proof claim is made.

## Why this strength would suffice

The corpus bound `|D(q)|<=24sqrt(q)` gives

`|K_d(M)| <= (24/sqrt(d)) sum_(k=d)^(M-1) sqrt(k)/(sqrt(k+1)+sqrt(k)) <=12 M/sqrt(d)`.

Consequently the diagonal divided by M^2 is at most `144 sum_(d<=M)1/d`.
SD1 would give the normalized complete Abel source `O(sqrt(log M))`. Mellin/Abel continuation
would then exclude every fixed exponent beyond the critical one. This implication uses the
same actual signed source, and must be wired to the corpus receiver before claiming Lean closure.
The arithmetic content is SD1 itself, not the elementary diagonal envelope.

## Attacks

1. Exhaustive finite counterexample search, initially M<=2^21, using exact piecewise-quadratic
   channel structure. Numerical results guide research only.
2. Expand the off-diagonal and retain gcd, quotient, squarefree and coprimality labels. The
   corpus identity `mu(br)mu(ar)=mu(ab)mu(r)^2` identifies orientation but does not sum it.
3. Test proposed source-shape proofs on nearby kernels before applying them to this D.
   A general-kernel failure does not refute SD1 for the literal divisor source.

The negative two-prime renewal determinant is not a proof of SD1: that determinant is evaluated
after complete renewal collapses to `exp(-ax)`, while SD1 concerns the unresolved inverse source.

## Verification protocol

See the frozen [experiment protocol](../2-fully-proven/computations/mobius-divisor-diagonal-dominance-2026-09-06/PROTOCOL.md).
No finite pass will be called an all-scale proof, and the factor one will not be adjusted after
a counterexample. The elementary diagonal bound alone is not recorded as new RH progress.
