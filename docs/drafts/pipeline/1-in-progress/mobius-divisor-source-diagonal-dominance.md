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

## Current evidence and formal boundary

SD1 survives exhaustive floating-point testing at all integers through 2,097,152. M=2 is exact
equality; the largest other ratio is 0.77306365027833565955 at M=17, independently checked at
60 and 100 digits. These checks do not prove SD1. Full data and audits are in the
[computation report](../2-fully-proven/computations/mobius-divisor-diagonal-dominance-2026-09-06/REPORT.md).

**SD2, independent stronger [BRIDGE], numerically rejected:** the margin
`E(M)=sum_d mu(d)^2 K_d(M)^2-S(M)^2` is nondecreasing for all M>=1. The first decrease is
M=4 to 5, about -0.01312330656601420691. There are 21,863 recorded decreases; the largest
absolute one occurs at M=1,851,018. Rejecting this monotone producer does not reject SD1 or
this RH branch. No damped monotonicity statement replaces the frozen claim.

The positive residue is an exact evolution retaining the signed mixed term. With
`C_d=mu(d)K_d`, `v_d=mu(d)D(floor(M/d))`, and `w=sqrt(M+1)-sqrt(M)`, Lean proves

`C_d(M+1)=C_d(M)+w v_d`,
`Q(M+1)-Q(M)=2w sum_d C_d(M)v_d+w^2 sum_d v_d^2`,

where Q is the complete arithmetic diagonal and the new terminal channel is zero.
[MobiusDivisorAbelDiagonalBound.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorAbelDiagonalBound.lean)
also proves `Q(M)<=144M^2 sum_(d<=M)1/d` unconditionally. No experimental result is used.
The numerical SD2 counterexample itself is not a Lean certificate. The signed total
off-diagonal upper bound and the subpower-loss continuation bridge remain open.
