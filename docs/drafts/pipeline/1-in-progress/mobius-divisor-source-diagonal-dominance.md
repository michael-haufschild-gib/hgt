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

The unconditional signed hyperbola estimate gives

`C_d(M)^2 <= 361 M sqrt(floor((M-1)/d))`,
`Q(M)=sum_(d<=M) C_d(M)^2 <= 722 M^2`,

where `C_d=mu(d)K_d`. Exact periodic cancellation is taken inside each time channel;
complete quotient blocks and the clipped final block are all retained.
`RHTower.sum_mobiusDivisorDilationChannel_sq_le_quadratic` in
`MobiusDivisorAbelQuadraticDiagonal` certifies the second inequality. The complete
[paper proof and Lean audit](../3-formalized/ccm-fu-signed-divisor-hyperbola-cancellation.md)
record the signed hyperbola argument.

Thus SD1 would directly imply `|S(M)/M|<=sqrt(722)` for M>=1. The existing
`riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded` receiver then applies; no
subpower-loss continuation is needed. The remaining arithmetic content is SD1 itself.
The quadratic diagonal bound does not establish it.

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
proves the exact successor laws and a harmonic envelope. The sharper
`Q(M)<=722M^2` is closed in `MobiusDivisorAbelQuadraticDiagonal.lean`, using signed
hyperbola summation. No experimental result is used in either proof.
The numerical SD2 counterexample itself is not a Lean certificate. The signed total
off-diagonal upper bound remains open; the diagonal needs no subpower-loss continuation.


**Other proposed producers:** arbitrary nonnegative decreasing time weights fail in Lean,
including some positive strictly decreasing geometric weights. Mixed positivity against every
flat prefix fails numerically at M=17,t=6; mixed positivity against every geometric kernel
fails numerically at M=1802,q=1/1000000, despite passing the initial grid through512. The
[obstruction card](../5-failed/mobius-divisor-decreasing-weight-producer.md) retains the exact
all-scale Abel prefix representation and states the separate proof statuses. These failures
do not refute SD1. A source proof must still control the total signed half-order pairing.
