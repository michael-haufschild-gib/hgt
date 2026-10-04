# RP68: separate absolute payment of complete prime-increment mixed work

- **ID:** RP68
- **Stage:** 5-failed, separate absolute-payment branch only
- **Type:** NO_GO with formalized positive admission classification
- **Source:** MobiusDivisorCriticalPrimeTailSource;
  MobiusDivisorCriticalRetainedPrimeProduct; RP67 joint-block calculation.
- **Target:** test separate absolute admission of the complete late-prime
  mixed work as a step toward native square-energy admission.
- **Surviving hard target:** estimate the whole joint signed square;
  Route RP is not retired.

## Fixed source and hard obligation

Use the existing a=criticalAbelLogProfile, v=criticalAbelLogVelocity and
M(u)=Sieve.mertensS(floor(exp u)). The literal square-root-core head F has

    F(t)=a(t)+J(t),
    J(t)=sum_(exp(t/2)<p<=exp(t)) a(t-log p)/p
        =integral_0^(t/2) v(s)*(M(t-s)-M(t/2)) ds.

Here F is normalized by exp(-3*t/2), not by exp(-t). The native critical
head is h(t)=exp(t/2)*a(t), so the required square measure is
exp((1-epsilon)*t)*a(t)^2 dt. Existing unweighted L1 admissions of a and v
are not admission in this measure.

Conjecture under attack: the joint expression

    integral_0^T exp((1-epsilon)*t)*(F(t)^2-2*F(t)*J(t)+J(t)^2) dt

has a finite T-independent upper bound for each epsilon>0. This is the
actual native energy; the purpose of the decomposition is to estimate
its arithmetic mixed work, not count the identity as payment.

## Prime-increment test

Write M(u)=log u+c+r(u) on u>0. The constant cancels exactly. The corpus's
integration-by-parts theorem gives J=K+R, with

    K(t)=integral_0^(t/2) a(s)/(t-s) ds,
    R(t)=integral_0^(t/2) v(s)*(r(t-s)-r(t/2)) ds.

Retaining the error before squaring gives

    a^2 = F^2-2*F*K+K^2 + 2*(K-F)*R+R^2.

Neither dropping R nor replacing it by a separately small unweighted
quantity establishes the required exponentially weighted estimate.
The current question is whether the complete mixed expression has an
arithmetic cancellation that survives finite-window integration.

## Current-source checks

The literal late-prime identity, exact stepwise Mertens integral, and
vanishing boundary products were read in CriticalPrimeTailSource.
CriticalRetainedPrimeProduct admits the retained first-moment source with
its actual cutoff; it does not assert square-energy admission.
The second-grade hyperbola identity retains the future-error pairing,
harmonic prime error and floor remainder; positivity of the floor term
does not remove either signed error term.

Previous turn RP67 produced no frontier theorem. No source estimate is
being treated as a premise. No numerical experiment, resource override,
or RH claim has been introduced.

## RP68 absolute mixed-work admission conjecture

The current-source second-order asymptotic gives t^2*J(t) -> -D/3,
D=divisorHarmonicBoundary>0. Test the proposed separate admission of
exp((1-epsilon)*t)*a(t)*J(t), for 0<epsilon<1/2.

Paper obstruction: eventual |J(t)| >= D/(6*t^2) makes this admission
imply native h in L1, since exp((1/2-epsilon)*t)/t^2 eventually dominates
a positive constant. The native/source difference is bounded by an
integrable decaying exponential. Thus the literal Route-P source would
also be L1. Its Laplace transform would be holomorphic for Re z>0 and
uniformly bounded up to the imaginary axis. The existing analytic
rigidity identifies this transform with the actual source continuation;
the existing unconditional Hardy-zero residue is nonzero. Multiplication
by the positive approach parameter gives both zero and that nonzero
residue, a contradiction.

This proof must establish L1 nonintegrability separately: the existing
L2 obstruction does not imply it. BochnerLaplaceHolomorphy supplies the
needed L1 holomorphy; no new analytic framework is required.

Positive survivor to audit: a two-sided eventual comparison, hence an
exact integrability classification at infinity, between the mixed density
and exp((1/2-epsilon)*t)*h(t)/t^2. The denominator concerns only infinity;
no admission at t=0 is inferred. This identifies the arithmetic
cancellation the joint square must retain. It does not pay the native
square or retire Route RP.

## Positive survivor: complete paper proof and Lean status

Let W_epsilon(t)=exp((1/2-epsilon)*t)*h(t)/t^2. The nonzero limit
t^2*J(t)->-D/3 proves J=Theta(1/t^2) at infinity. Multiplying both sides
by exp((1-epsilon)*t)*a(t), including its zeros and sign, gives
mixedWork_epsilon=Theta(W_epsilon). The exact finite-prime expression is
measurable: freeze the natural cutoff, take its finite measurable sum,
then compose with floor(exp t). Consequently mixedWork_epsilon is
absolutely integrable at infinity iff W_epsilon is. This is the precise
positive classification exposed by the obstruction; no value at t=0 is
used. For epsilon<1/2, t^2=o(exp((1/2-epsilon)*t)) makes h=O(mixedWork).
Continuity of h fills the compact head. Any late absolute mixed budget
would therefore imply h in L1, contradicting the residue proof above.

The paper proof is dependency-closed. All three affected Lean leaves
passed foreground final audits using lake --old env lean with explicit
olean output. Both new modules are wired into RHTower; no umbrella build
was run. All 14 audited public theorems have only propext, Classical.choice,
and Quot.sound. No heartbeat
override or premise added to an unconditional capstone.
Global lint exits1 on14 unrelated unreachable modules; neither new leaf
nor the edited leaf has a lint error. This is not a global lint pass.

New leaves:

- RoutePNativeCriticalL1Nonintegrability: unconditional source and native
  L1 nonintegrability.
- RoutePNativeLatePrimeMixedAdmission: exact actual increment, scaled
  limit, Theta comparison, absolute-admission iff at infinity, and
  nonintegrability even on every late ray for epsilon<1/2.

Next conjecture RP69 tests bounded signed partial mixed work. Absolute
nonintegrability alone does not answer that question. Its card preserves
the actual prime-removal jumps and identifies the missing variation and
integration-by-parts arguments.
