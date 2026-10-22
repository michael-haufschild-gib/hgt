# RP-54: joint von Mangoldt forcing at the native cutoff

Status: active hard-frontier trial. No new Lean result claimed.
Route RP, target unconditional RH. Previous RP-53 supplied failed-estimate
diagnostics, not a new frontier theorem. Positive-damping negative-work
payment, signed high-LCM control, and both history debts remain open.

## Finite joint identity and the sign test

Write U for divisorContinuousUnitHead, H for mobiusDivisorFullHead,
h(t)=exp(-t)*H(exp(t)). Set

  R(x)=sum_{d<=x} mu(d)*sqrt(d)*log(x/d)*U(x/d),
  r(t)=exp(-t)*R(exp(t)).

The corpus identity mu*log=-Lambda*mu, applied in each coefficient
variable before any limit, gives

  sum_{d<=x} mu(d)*sqrt(d)*log(d)*U(x/d)
    = -sum_{n<=x} Lambda(n)*sqrt(n)*H(x/n),

and therefore

  t*h(t)^2 + sum_{n<=exp(t)} Lambda(n)/sqrt(n)
      *h(t)*h(t-log(n)) = h(t)*r(t).

Every term is physical and finite. Multiplication by exp(-epsilon*t)
and integration from0 toT yields the joint forcing identity, retaining
lower endpoint log(n) and upper endpoint T in every prime-lag integral.
This is a paper calculation from finite convolution, not a new payment.

For one retained lag l=log(n), completing the square gives exactly

  2*integral_l^T exp(-epsilon*t)*h(t)*h(t-l) dt
    = integral_l^T exp(-epsilon*t)*h(t)^2 dt
      + exp(-epsilon*l)*integral_0^(T-l) exp(-epsilon*s)*h(s)^2 ds
      - integral_l^T exp(-epsilon*t)*(h(t)-h(t-l))^2 dt.

Thus the nonnegative difference energy enters the prime correlation with
a minus sign. The joint identity alone cannot provide the required upper
energy payment by dropping it. Its coefficient sums also grow with the
physical horizon. No separate absolute forcing bound has been assumed.

## Zero-moment trial: retained terminal square

Set a(t)=criticalAbelLogProfile(t)=exp(-t/2)*h(t), and let
F(t)=integral_t^infinity a(s) ds. The proved zero moment gives F(0)=0.
The actual prime-lag sum has the normalization

  sum Lambda(n)/sqrt(n)*h(t-log(n))
    = exp(t/2)*sum Lambda(n)/n*a(t-log(n)).

Thus its continuum main measure is the harmonic von Mangoldt measure,
with Lebesgue main term. Its convolution is integral_0^t a=-F(t).
Writing kappa=1-epsilon, the resulting continuum contribution is exactly

  -integral_0^T exp(kappa*t)*a(t)*F(t) dt
    = exp(kappa*T)*F(T)^2/2
      - kappa/2*integral_0^T exp(kappa*t)*F(t)^2 dt.

This finite integration by parts retains the terminal square. Neither
the zero moment nor the polynomial source moments bound that square
uniformly in T for 0<epsilon<1. No estimate of the arithmetic remainder
has been proved. This rejects the proposed deletion of the moment tail,
not the desired native energy bound.

## Native self-convolution trial

The following is a paper derivation, not a Lean-audited theorem. All
functions and measures in this paragraph are extended causally by zero.
Let b(t)=criticalAbelLogDefect(t), v(t)=criticalAbelLogVelocity(t),
u0(t)=exp(-3*t/2)*U(exp(t)), and gamma=Euler's constant. Define locally
finite measures J=sum_(n>=1) delta_log(n)/n and
L=sum_(n>=1) Lambda(n)*delta_log(n)/n. Native reconstruction gives
J*a=u0. The actual source equation is b=2*a'+3*a, with a(0)=0.

Between jumps b'=-b; the jump at log(n), n>=2, is (Lambda(n)-1)/n.
The causal jump at zero is b(0)=2*gamma-1. Consequently

  Db+b = L-J+2*gamma*delta_0,
  L*a = u0+2*(v*v)+5*(v*a)+3*(a*a)-2*gamma*a.

Here * between functions denotes causal convolution, not autocorrelation.
The delta_0 correction is essential: J includes its n=1 atom. The second
derivative of a*a is v*v because a(0)=0; no derivative of the discontinuous
velocity is required in the displayed regular-function identity.

Existing absolute admission of a and v, and the unit-source bound, admit
the right side in unweighted L1. This is an admission at the source
normalization. It does not admit the required work

  integral_0^T exp((1-epsilon)*t)*a(t)*(L*a)(t) dt.

After exponential conjugation f(t)=exp(kappa*t/2)*a(t), its convolution
part is cubic, pairing f with

  2*(f'*f')+(5-2*kappa)*(f'*f)
    +(3-5*kappa/2+kappa^2/2)*(f*f).

No sign follows from the L1 admissions. Young estimates on this expression
require exponentially weighted norms of a or v, which are not supplied
by the existing polynomial moments. In particular, small unweighted
tails do not pay an exponential factor at an unbounded physical cutoff.
The exact remainder r0=exp(-t/2)*r is still the native inverse-dilation
transform of t*u0. Replacing it by a separately admitted forcing would
discard the same missing arithmetic cancellation.

Assessment: three concrete source-based trials (square completion,
zero-moment subtraction, self-convolution) identified retained terms but
did not prove a new frontier inequality. No identity-only Lean leaf is
being added. Route RP remains active; no no-go or retirement is claimed.

## Corpus audit

All four owned searches completed with exit0. Every candidate, source
argument, proposed ingredient set, and proof-idea section was inspected.
Returned Lean evidence was source-only; no proposed recipe was accepted
as a checked proof. Semantic coverage was unmeasured and background
refresh incomplete throughout.

- Joint forcing55251: partial=false, no errors or unfinished stages;
  query generation1191031, coverage1191056/current1191058,64637files,
  zero pending files. Older-coverage and semantic-unavailable warnings.
- Native tail16315: partial=false, no errors or unfinished stages;
  query1191072, coverage/current1191087,64640files,zero pending files.
- Self-convolution45135: partial=true; filter_and_judge returned
  incomplete/malformed local-model JSON. Query1191114,
  coverage/current1191132,64645files,zero pending files. Available hits
  suffice to inspect the literal profile primitive and source convolution;
  they do not certify the new paper identity or an energy estimate.
- Absorption51133: partial=false, no errors or unfinished stages;
  query1191162, coverage1191185/current1191186,64649files,zero pending.
  Its proposed tail/graph-energy recipe changes carriers and leaves
  comparison hypotheses; it does not pay the native exponential weight.

Relevant sources read include DeningerVonMangoldtMoebiusConvolution,
LogarithmicCoprimeEnergy, MobiusDivisorCriticalMellinMass,
MobiusDivisorCriticalPrimeTailError,
MobiusDivisorCriticalRetainedPrimeBoundary,
MobiusDivisorCriticalCompensatedCauchy,
MobiusDivisorCriticalSourceAutocorrelation,
MobiusDivisorCriticalLogProfilePrimitive, and
MobiusDivisorCriticalAbelBoundaryMoments. Existing undamped native balance
and the route ledger were checked. No Lean source changed or build ran.

Next mathematical test: retain the inverse-dilation remainder r0 jointly
with the prime term, and seek a finite-cutoff cancellation in their
bilinear kernel. Estimating either factor through unweighted source
admission is the failed step; repeating it with more polynomial moments
will not resolve the exponential-weight gap.

Cleanup: all owned searches terminal; four temporary research JSONs
removed. Scoped whitespace check passed. No subagents, computations,
resource-limit overrides, builds, commits, or pushes.
