# RP-48: common-source control of the core/late-prime remainder

Status: paper attempts; no new bound or Lean theorem. Route RP remains open.

The RP-47 initial-prime full-ray escape theorem rules out a replacement
energy. This attempt keeps the physical cutoff and the full late-prime
correction. The hard target is signed payment of the native history, not
another estimate for the replacement family.

## Exact source and attempted estimate

The corpus's criticalContinuousAbel source H has logarithmic profile
g(t)=exp(-3*t/2)*H(exp t), defect q(t)=exp(-t)*psiDefect(floor(exp t)),
and velocity v=q/2-3*g/2. Let m be criticalMertensLogError. The read
MobiusDivisorCriticalMovingHeadAsymptotic decomposition is

    exp(-3*t/2)*F(exp t)
      = g(t) + integral_0^(t/2) g(s)/(t-s) ds
        + integral_0^(t/2) v(s)*(m(t-s)-m(t/2)) ds.

At integer cutoffs F is the actual square-root core; the two integrals
retain its complete late-prime child correction. Both core and correction
have the same large negative leading term. Their separate asymptotics do
not bound the native difference. The source moment integral g=0 cancels
the first continuum term; its first logarithmic moment is nonzero and
already produces the known next term. This is existing corpus knowledge.

A critical square estimate would have to control, for each0<epsilon<1,

    integral_0^T exp((1-epsilon)*t)*g(t)^2 dt

uniformly in T. All-polynomial logarithmic moments or a t^2 remainder limit
do not supply this exponentially weighted bound. Subtracting the two
integrals from the displayed identity only recovers g; it is not an
independent estimate of the forcing.

## Common-source symmetrization attempt

The candidate was to relate m and q through the same actual prime entries,
then turn the reflected mixed work into a dissipative square. The floor in
q cannot be removed. Between integer entries q'=-q, and at log n, n>=2,
its jump is (Lambda(n)-1)/n. The resulting distributional diagnostic on
t>0 is

    dq + q dt = sum_(n>=2) (Lambda(n)-1)/n delta_(log n),
    t dm = dq + q dt + sum_(n>=2) delta_(log n)/n - dt
                 - sum_(proper prime powers n) Lambda(n)/n delta_(log n).

These are paper bookkeeping identities, not new formal statements.
Integer-entry forcing, the floor, and proper prime powers remain present.
No all-real bridge or missing distributional regularity lemma is assumed.

Even the smooth comparison calculation retains a midpoint boundary. For
a C^2 profile with g(0)=0, put C=g*g and h=t/2. Integration by parts gives

    integral_0^h g(s)*(2*g''+5*g'+3*g)(t-s) ds
      = C''(t)+(5/2)*C'(t)+(3/2)*C(t)
          -2*g(h)*g'(h)-(5/2)*g(h)^2.

The native profile has entry jumps in its velocity, so using this formula
there requires the corresponding Stieltjes/jump audit. More importantly,
the retained midpoint terms have no proved critical payment. No absorption
estimate was obtained, even before that formalization obligation.

MobiusDivisorCriticalRetainedPrimeBoundary keeps p<=y inside its transform.
Its proved boundary slope is from nonnegative damping. Replacing the
ordered prime sum by a full prime-zeta factor or continuing it across the
boundary would remove the unpaid ordered work. Neither step is used.

## Other finite-cutoff checks

The short reciprocal-Mobius square idea retains a product-dependent
sawtooth pairing. In the terminal band the kernel is X/(a*b)-1, so its
literal quadratic contribution is

    X*(sum mu(a)/a)^2 - (sum mu(a))^2.

Both squares and the mixed head blocks remain. The full first-half
reflection also retains its errors. RP-3, RP-10, RP-11, and RP-16 already
tested the proposed rank-square or reciprocal-moment cancellation; those
identities are not a new advance here.

The exact second-grade hyperbola law retains the future-error pairing
alongside the Chebyshev square. Its nonnegative floor remainder does not
bound that pairing. The exact Euler-renewal law retains signed deficit
values. Positive-renewal rigidity applies to comparison profiles, not to
the native signed source. No coercive quantity or critical estimate was
constructed from these laws.

Contribution assessment: no frontier bound, source-domain admission,
unconditional RH proof, or falsification was established by RP-48. These
diagnostics delimit failed proof steps, not a retirement theorem for the
native route. No identity-only Lean leaf is warranted. The next estimate
must retain the ordered prime work, midpoint boundary, integer entries,
and proper-power correction in one signed expression.
