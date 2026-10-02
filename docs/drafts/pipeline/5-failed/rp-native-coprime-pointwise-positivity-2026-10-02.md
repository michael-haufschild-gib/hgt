# RP: native coprime pointwise positivity fails

- **ID:** RP-44-native-coprime-sign
- **Stage:** 5-failed
- **Type:** FALSIFIED (final leaf and axiom audits passed)
- **Source:** rp-unconditional-history-floor-loop-2026-10-01.md, RP-44;
  rp-native-coprime-abel-budget-2026-10-02.md
- **Statement tested:** the complete coprime energy of the actual full
  divisor-head profile is everywhere nonnegative at positive times.

## Exact source and proof

Write U=divisorContinuousUnitHead, H=mobiusDivisorFullHead,
u(t)=sqrt(exp(-t))*H(exp(t)), and W(y)=y*U(1/y)^2. Let
A(y)=sum_n mu(n)*W(n*y), retaining every term. Exact finite identities give

    A(exp(-t)) = coprimeEnergy(u,t)
              = u(t)^2 + coprimeCross(u,t),  t>=0.

The whole source has an absolutely admitted Mellin integral for Re(s)>1:

    Mellin(A,s) = Mellin(W,s)/zeta(s).

W is nonnegative, bounded, supported below1, and has positive integral C.
Its Mellin transform is holomorphic for Re(s)>0. The filled zeta pole gives

    Mellin(A,1+epsilon) -> 0,
    Mellin(A,1+epsilon)/epsilon -> C>0.

If A were nonnegative on(0,1), its real Mellin integral would be antitone
in epsilon. Its zero right boundary limit would force every such integral
to be nonpositive, contradicting the positive first-order coefficient.
Hence A(y)<0 for some0<y<1. Transport t=-log(y) proves

    coprimeCross(u,t) < -u(t)^2  for some t>0.

No separate endpoint-square integrability, critical moment, zero-free
region, or RH premise is used. No numerical example is used.

## No-go closure

- **Exact killing theorem:** `RHTower.nativeCoprimeCross_lt_neg_square`
  in `RoutePCoprimeSquareSign.lean`; even the pointwise lower bound by
  minus the endpoint square fails on the actual arithmetic profile.
- **Strongest positive survivor:** absolute admission and the exact
  positive first-order coefficient of the complete native signed energy,
  `RHTower.nativeCoprimeEnergy_hasMellin`,
  `RHTower.nativeCoprimeEnergy_simpleJet`, and
  `RHTower.routePCoprimeSquareMass_pos`.
- **New insight:** this signed coprime form is negative on the native
  arithmetic history, not just on synthetic vectors. Any useful lower
  bound must allow this deficit. The admitted combined budget remains
  available, but does not control the positive endpoint by itself.
- **Paper status:** dependency-closed proof above, using the corpus's
  unsigned-source ceiling, finite coprime identity, and Mellin interchange.
- **Lean status:** all three final leaf audits passed using lake --old env
  lean. Ten principal positive/source/sign theorems printed only propext,
  Classical.choice, Quot.sound. All leaves wired into the umbrella, which
  was not built. Global lint still fails on eleven pre-existing unreachable
  modules outside this change; no new leaf is reported.

Only the pointwise positivity candidate is retired. The original RH goal,
both history squares, and a useful integrated signed lower bound remain
open. The stronger eventual negative finite-prefix cross-work statement
from the parent card remains paper-only; it is not asserted by this card.

## Log

- 2026-10-02 — Corpus search, source-faithful Mellin proof, native transport,
  and native sign obstruction. No full or umbrella build, no extra axioms,
  no heartbeat override. Final leaf and axiom audits passed. Pointwise
  candidate closed with its audited positive source-budget survivor.
