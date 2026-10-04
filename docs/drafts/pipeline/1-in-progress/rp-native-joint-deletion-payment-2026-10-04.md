# RP67: absolute payment through joint native prime deletion

- **ID:** RP67
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** RoutePNativeUndampedBalance; RoutePNativeBiasedMeanComparison;
  RoutePFinitePrimeCovariance; current RP frontier map.
- **Target:** for each epsilon>0, bound the full native square energy
  integral exp(-epsilon*t)*h(t)^2 on all finite physical windows.

## Hard gap and previous progress

RP66 paid the extra covariance cost relative to the native head. It did
not pay either norm absolutely. Positive-damping negative coprime work,
signed high-LCM cancellation, and both physical history debts remain open.
No RH conclusion follows. This attempt must supply an absolute signed
estimate, not another comparison or conditional receiver.

## First test: absorb negative work from the admitted balance

Write h=routePNativeCriticalProfile, C=routePNativeCriticalCoprimeWork,
B=h^2+C. The corpus proves B integrable with total zero and C_+ integrable.
The exact identity C_-=h^2+C_+-B leaves coefficient one on h^2.
Multiplying by positive damping preserves that coefficient. Thus this
identity alone supplies no strict absorption. This is an applicability
diagnosis; it does not falsify positive-damping admission.

## Active test: joint prime deletion

For a finite core, write D_p f(t)=f(t-log p), q_p=p^(-(1+epsilon)/2),
theta_p=1-1/p. The exact covariance update retains
-2*theta_p*q_p times mixed parent/child work plus q_p^2 times child energy.
Seek a joint signed bound across prime admissions at the physical horizon.
Independent two-channel savings are already excluded by RP63; finite-core
full-ray replacement is already excluded by RP47. Neither will be assumed.
All child cutoffs, mixed terms, and native source coefficients must remain.

## Research audit

The native-payment, history-floor, and positive-damping corpus searches
all completed, partial=false, errors=[], unfinished_stages=[]. Full source
inventories: 65143, 65145, 65147 files, zero pending. Relevant hits are
source-only; compiler coverage is mostly pending/stale. Refresh reports
background_indexer_running. Candidate statements, source arguments,
proof ideas and ingredient sets were inspected. Generated combinations of
finite-window integrability with covariance comparisons do not prove the
absolute bound and were rejected.

## Status

Active mathematical attempt. No new theorem or frontier payment yet.
No production Lean edits, build, computation, added premise, or axiom.

## Joint-block calculation

Retain a parent f after the small core, and a block Q such that every
distinct p,q in Q has log(p)+log(q)>=T. Causality kills every double child
on [0,T]. Put f_p(t)=f(t-log p), b_p=theta_p*q_p and
w_p=(1-theta_p^2)*q_p^2. The complete block covariance is therefore

    (f-sum_p b_p*f_p)^2 + sum_p w_p*f_p^2.

Its change from f^2 is

    -2*f*L + L^2 + sum_p w_p*f_p^2,
    L=sum_p b_p*f_p.

This paper calculation follows by retaining the empty and singleton terms
in the existing cofactor-square expansion. In particular L^2 retains all
different-prime child products. The sign needed for absolute payment is
the joint parent/child estimate
2*integral(f*L) >= integral(L^2+sum_p w_p*f_p^2) minus a paid allowance.
Completing this square returns the unpaid final native mean; it supplies
no strict contraction. No sign was assigned to the mixed integral.

Actual corpus applicability checks:

- MobiusDivisorGrowingSignedPrimeBatches and CoupledTwoPrimeBatches give
  growing selected batches; they do not consume every remaining prime.
- MobiusDivisorFixedCoreMovingPrimeEnergySublinear fixes the processed
  core and bounded quotient depth. Its threshold depends on that core.
- The complete terminal-order theorem bounds prefixes by the maximum of
  initial and final energies; its iff theorem retains the final bound.
- Adaptive monotone prime elimination already fails on the actual source
  in MobiusDivisorAdaptivePrimeEnergyObstruction. No fresh no-go is claimed.
- MobiusDivisorCriticalClockProductTransport retains exactly the signed
  mixed correlation in its density-weighted balance.

## Radial-thinning test

A proposed route from the admitted diagonal to the fully correlated
source would vary a common prime bias from zero to one. The half-bias
coefficient is exactly the corpus's halfSelectionMoebiusWeight, not a
new coefficient system. Its Euler product F satisfies

    F(s)^2*zeta(s) = product_p (1+p^(-2s)/(4*(1-p^(-s)))).

MobiusHalfSelectionEulerProduct and EulerCorrection already prove this
identity and the correction's analytic nonzero germ at one.
MobiusHalfSelectionPoleObstruction and GrowthObstruction already rule out
a linear bound for the literal half-selected divisor head and any fixed
averaged-energy multiple of the original diagonal. Thus radial thinning
cannot be treated as an already-paid interpolating family. This is a
recovered obstruction, not new knowledge or a new Lean result. The RP66
prime-dependent bias remains different and preserves the original debt.

## Additional search audit and outcome

Joint-deletion, complete-order and thinning searches completed with
partial=false, errors=[], unfinished_stages=[]. Inventories65149,65150,
65151, zero pending; source-only relevant hits and background refresh.
The broad thinning search returned poor matches; direct source-text
search located the four exact HalfSelection modules. Statements,
source_arguments, proof_ideas and ingredient_sets were inspected.
Generated unrelated symmetry/Mellin suggestions supplied no native bound.

No new critical inequality was proved in this pass. None of these tests
retires Route RP. No duplicate obstruction, identity-only leaf, weakened
receiver, or numerical bound was formalized. The next hard attempt must
estimate the joint parent/complete-child mixed work itself, retaining the
native residual, rather than infer it from a choice of prime order or
independent averaging. Positive-damping negative work, signed high-LCM,
both history debts, and RH remain open. Goal active; no external blocker.
