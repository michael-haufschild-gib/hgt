# RP-62: reciprocal Bernoulli boundary and terminal-square payment

Route RP. RP-61 made no frontier progress. Target the original native
history floor, including both debts and signed high-LCM work; fixed
positive-damping negative work remains open.

Starting from RP-61, retain q(d)=mu(d)log(d), both cutoffs N and N^2,
the exact Bernoulli boundary Q(t)=({t}^2-{t})/2, and the terminal square.
Conjecture: divisor regrouping of the boundary and integral tails yields
a signed payment inequality for the complete expression. No sign of
an isolated component, critical admission, or source bound is assumed.

## First paper calculation: finite floor regrouping

For X>=1 and a real parameter z, set

    F_z(X)=sum_(d<=X) mu(d)*d^(1+z)*Q(X/d),
    g_z(n)=sum_(d|n) mu(d)*d^z.

Writing m=floor(X/d) gives

    d*Q(X/d)=X^2/(2d)-X/2-X*m+d*m*(m+1)/2.

The last two terms regroup exactly into a Riesz sum:

    F_z(X)=(X^2/2)*sum_(d<=X) mu(d)*d^(z-1)
           -(X/2)*sum_(d<=X) mu(d)*d^z
           -sum_(n<=X) (X-n)*g_z(n).

This finite identity makes no infinite exchange. At z=0, g_0 is the
Dirichlet unit, hence F_0(X)=X^2*(sum mu(d)/d)/2-X*(sum mu(d))/2-X+1.

The corpus logarithmic derivation gives g'_0=-Lambda and
g''_0=Lambda*Lambda-Lambda.log. Consequently, with

    T(X)=sum_(d<=X) mu(d)*d*log(d)*log(X/d)*Q(X/d),
    L_j(X)=sum_(d<=X) mu(d)*log(d)^j/d,
    C_j(X)=sum_(d<=X) mu(d)*log(d)^j,

one obtains on paper

    T(X)=(X^2/2)*(log(X)*L_1(X)-L_2(X))
          -(X/2)*(log(X)*C_1(X)-C_2(X))+S(X),
    S(X)=sum_(n<=X) (X-n)*
            [(Lambda*Lambda)(n)+Lambda(n)*log(X/n)] >= 0.

The next task is to test this positive term against the original square,
including every integral tail and smooth moment. The displayed finite
identity alone is not a critical bound and is not Lean certified here.

## Trial 2: integral-tail completion fails; keep Euler summation finite

Define U_X(u)=sum_(d<=X) mu(d)*d*log(d)*Q(u/d) and
T_X(u)=sum_(d<=X) mu(d)*d*log(d)*log(u/d)*Q(u/d).
The RP-61 tail formula involves U_X(u), T_X(u) for u>=X. The finite
floor identities above instead apply to U_u(u), T_u(u). These are
different heads, even though they agree at u=X.

Extending the tail to the complete head is not an admitted shortcut.
For each added d>X, its integrated contribution to the completed
combination, before the overall sign, would be

    q(d)*[kappa1/sqrt(X*d)+kappa0/X],
    kappa1=integral_1^infinity Q(t)*(3log(t)/4-2)*t^(-5/2)dt,
    kappa0=integral_1^infinity Q(t)*t^(-2)dt < 0.

Each of these two constant integrals is absolutely admitted. The
strict sign of kappa0 follows from Q<=0 and Q<0 on (1,2). Along
primes d, q(d)=-log(d), so the displayed added terms do not tend to
zero. Thus their ordinary infinite sum cannot supply the missing
completion. This is a paper obstruction to this exchange, not an
obstruction to the original finite-head integral.

The repair is to retain the finite Euler formula before introducing
the constants A,B and their tails:

    P(Y)=Y(logY-3)+4sqrtY-1-Q(Y)logY/(2Y)
           -sqrtY*integral_1^Y Q(t)*a'(t)dt
           +integral_1^Y Q(t)*b0'(t)dt.

Changing variables u=d*t now has 1<=d<=u<=X. Every regrouped divisor
head is complete at u, and all exchanges are finite. This fixes the
admission defect without discarding any physical terms.

## Trial 3: test the full positive term against its actual compensator

Write A1(X)=sum_(n<=X)(X-n)*Lambda(n), and keep S from Trial 1.
Substitution of the finite floor identities gives on paper

    R(X)/X = S(X)/(2X^2)
       +(3/(4sqrtX))*integral_1^X S(u)*u^(-5/2)du
       +integral_1^X A1(u)*
          [-2*u^(-5/2)/sqrtX+u^(-2)/X]du.

The A1 kernel is strictly negative for 1<=u<=X. Hence positivity of
S by itself does not pay the joint expression. Its first-grade part
is exactly the amount needed to cancel this compensator.

To see the cancellation with all coefficients retained, split

    S=S0+S1,
    S0(X)=sum_(n<=X)(X-n)*(Lambda*Lambda)(n),
    S1(X)=sum_(n<=X)(X-n)*Lambda(n)*log(X/n).

For a fixed n<=X, put v=X/n. The first two operators applied to the
S1 coefficient give

    X^(-1)*[(8/3)*sqrt(v)-3-log(v)+1/(3v)].

The A1 integral gives exactly its negative. The resulting formula is

    R(X)/X=S0(X)/(2X^2)
             +(3/(4sqrtX))*integral_1^X S0(u)*u^(-5/2)du,

which is precisely the positive Abel representation of the existing
Lambda*Lambda source. This is a successful algebra check but no new
source estimate. The native terminal square remains unpaid. The
positive survivor of this attempted sign argument is the already
known nonnegativity of Lambda and Lambda*Lambda, not extra coercivity.

This calculation does not rule out a critical bound for the complete
source. It rules out crediting the isolated positive S1 term while
omitting its exact compensator. No RH no-go is asserted.

## Next hard conjecture: preserve quadratic prime-label information

The scalar regrouping above collapses the quadratic information back
to the original source. The corpus's finite prime-label energy retains
that information through symmetric differences of prime supports.
Read MobiusDivisorBernoulliPrimeEnergy and
UniformPrimeSubsetBooleanInversion; the latter isolates every exact
symmetric-difference packet. Also read the actual half-selection
growth obstruction: independent probability 1/2 has no fixed diagonal
energy ceiling. Reusing that averaging would repeat a proved failure.

A different paper candidate selects each prime p with probability
theta_p=1-1/p. At finite cutoff the full-selection event has weight
product_p theta_p, and the exact averaged pair kernel is
product_(p in primeFactors(d) symmetricDifference primeFactors(e)) theta_p.
Its mean-head coefficient is mu(d)*product_(p|d)(1-1/p).

The local Euler factor is

    1-(1-1/p)*p^(-s)
      =(1-p^(-s))*(1+p^(-s)/(p*(1-p^(-s)))).

The correction product is absolutely convergent and nonvanishing on
Re(s)>0: its deviation from one is bounded on compact sub-half-planes
by a constant times p^(-1-Re(s)), and neither its numerator nor its
denominator vanishes there. Thus this bias preserves the native
1/zeta factor instead of introducing the artificial half-selection
singularity. This is only a paper admissibility check; it proves no
energy bound and removes no native zero obstruction.

The new hard conjecture is a critical bound for this complete weighted
selection energy with the physical cutoff and all residual fibres
retained. The mean-head term cannot be assumed bounded. The next turn
must derive and test the full covariance decomposition before treating
the bias as a payment mechanism.

## Search audit and outcome

Two direct documented deep searches completed with terminal exit 0:

- Mobius reciprocal Bernoulli boundary / terminal square: query
  generation 1215960, coverage=current 1215970, 65043 files.
- Signed Route-P source / prime renewal: query generation 1216045,
  coverage=current 1216046, 65046 files.

Both reported partial=false, errors=[], no unfinished stages, zero
pending inventory files. Semantic coverage was unavailable/not
measured; background refresh was incomplete. Compiler coverage was
predominantly pending/stale/unavailable, and retrieved candidates and
source arguments were source-only. Generated ingredient sets did not
establish a critical bound. Fixed-modulus positive renewal rigidity
explicitly leaves the signed Chebyshev source estimate open.

No frontier bound, RH proof/falsification, or new Lean theorem. No Lean
edit/build or umbrella change. No new lint/axiom certificate is claimed.
The exact computations here are symbolic paper derivations, with no
numerical experiment. All hard RP gaps remain open; goal active.
