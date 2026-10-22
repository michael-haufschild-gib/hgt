# RP-60: finite reciprocal-cutoff kernel payment

Route RP. RP-59 supplied paper identities but no frontier estimate.
Hard target: pay the native centroid and square debts, retaining the
signed high-LCM/cross-scale work and every positive damping.

Continue the exact reciprocal pairing from RP-59. At alpha=1/2 write
E=psi-id, F(v)=sum_(d<=v) Lambda(d)/sqrt(d)-2sqrt(v),
T(N)=integral_N^infinity E(u)*u^(-3/2)*F(N^2/u) du.
The common far tail cancels from T(2N)/(2N)-T(N)/N. Expand the entire
finite prime/background kernel, then test a signed payment law together
with second-grade discrepancy and the original variance coefficients.
No componentwise sign, norm replacement, or critical bound is assumed.

## Trial 1: expand the complete finite difference

Paper derivation, not Lean certified. Put M(v)=sum_(d<=v) Lambda(d)/sqrt(d)
and f(N)=T(N)/N. Expanding F in its exact finite prime sum gives

    f(N)=P(N)-2*integral_N^infinity E(u)/u^2 du,
    P(N)=N^(-1)*sum_(d<=N) Lambda(d)/sqrt(d)
                    *integral_N^(N^2/d) E(u)*u^(-3/2) du.

Hence the complete difference is finite:

    f(2N)-f(N)=P(2N)-P(N)+2*integral_N^(2N) E(u)/u^2 du.

Equivalently its kernel against E(u) is

    2/u^2-M(N^2/u)/(N*u^(3/2)),             N<=u<2N,
    [M(4N^2/u)/2-M(N^2/u)]/(N*u^(3/2)),    u>=2N.

The second expression vanishes beyond 2N^2 because Lambda has no
support below 2. In particular the continuous background on [N,2N]
cannot be dropped when canceling the common far tail. No sign of this
finite native pairing has been proved.

One invalid shortcut was excluded during the derivation: expanding both
E and F into an unbounded double signed-measure integral and invoking
absolute Fubini loses the inverse-square error cancellation. The absolute
variation at infinity would have a harmonic tail. The finite difference
above, or a finite prime sum with its explicit background, is the admitted
way to expand the expression.

## Trial 2: exact prime-pair kernel and its endpoint deficit

For a,b>=1 define

    k_N(a,b)=(2/N)*max(1/sqrt(b*max(N,a))-1/N,0),
    K_N(a,b)=(k_N(a,b)+k_N(b,a))/2.

The finite prime-pair part of P(N) is sum Lambda(a)*Lambda(b)*K_N(a,b).
Its continuous background is exactly

    -2*sum_(d<=N) Lambda(d)/d+2*M(N)/sqrt(N).

The prime-pair difference K_(2N)-K_N has mixed-sign diagonal entries.
For a<=N/2 its diagonal is negative; for N<a<2N it is positive.
This is a paper diagnostic for the proposed direct Gram argument, not
a sign claim for the complete native pairing with background included.

A sharper positive comparison survives on paper. Let R=a*b. Then
K_N(a,b)<=K_N(R,1), and the exact nonnegative deficit is

    N^(-3/2)*(1-1/sqrt(a))*(1-1/sqrt(b)),       R<=N,
    N^(-2)*(sqrt(N/a)-1)*(sqrt(N/b)-1),        N<R<=N^2, a,b<=N,
    0,                                       otherwise.

The first case follows from (sqrt(a)-1)*(sqrt(b)-1)>=0; the second
from (sqrt(N)-sqrt(a))*(sqrt(N)-sqrt(b))>=0. If one factor exceeds
N, the other factor's kernel is zero and the surviving term equals the
endpoint kernel. If R>N^2, both kernels vanish. All maximum cutoffs
are retained in this comparison.

This is not yet the desired estimate: the endpoint itself carries the
full second-grade prime convolution up to N^2.

## Trial 3: sum the positive deficit with all physical coefficients

Write b(r)=(Lambda*Lambda)(r), C(x)=sum_(r<=x)b(r),
B(x)=sum_(r<=x)b(r)/sqrt(r), and Z(N)=sqrt(N)*M(N)-psi(N).
The low-product correction in the preceding piecewise formula depends
only on R. It cancels exactly against the corresponding part of the
endpoint sum. The resulting finite identity is

    sum Lambda(a)*Lambda(b)*K_N(a,b)
        =B(N^2)/N-C(N^2)/N^2-Z(N)^2/N^2.

After restoring the continuous background and the admitted harmonic
tail, this becomes

    f(N)=B(N^2)/N-C(N^2)/N^2-2log(N)+2gamma+3
            -(Z(N)/N-1)^2.

Since Z(N)/N-1=A_(1/2)(N)/(2sqrt(N)), the rectangle square is exactly
the integrated-error square from RP-59. It supplies no independent
positive term for absorbing the reciprocal pairing. The endpoint
comparison therefore returns the original signed second-grade Riesz
error minus its square, with no critical estimate. The full native
variance still retains its additional square debt and centroid excess.

## Trial 4: retain the exact arithmetic coefficient identity

DirichletLogDerivation.lean proves b+Lambda*log=(log^2)*mu, with the
first product pointwise and the last Dirichlet convolution. Thus, for
W_N(r)=1/(N*sqrt(r))-1/N^2 on 1<=r<=N^2, the unpaid product source is

    sum_(dk<=N^2) mu(d)*log(k)^2*W_N(d*k)
       -sum_(r<=N^2) Lambda(r)*log(r)*W_N(r).

Both terms must stay coupled. A paper integral check for the inner
smooth profile, Y=N^2/d, gives

    integral_1^Y log(t)^2*(sqrt(Y/t)-1) dt
       =Y*(log(Y)^2-6log(Y)+14)-16sqrt(Y)+2.

This does not estimate the original discrete sum: its Euler summation
remainder and the coupled Lambda*log term remain. Bounding them
separately by the coarse Selberg result gives the already excluded
noncritical estimate. No sign or critical upper bound for their joint
remainder has been established.

## Status and next conjecture

No new critical bound, RH proof, or falsification. No Lean edits/builds;
paper comparisons are not promoted as frontier theorems. No route is
retired. The positive endpoint comparison and exact rectangle square
are retained for the continuing argument, not treated as a payment law.

Next attack: the coupled Mobius-log-squared and Mangoldt-log Riesz
source with the exact discrete remainder retained. Seek a signed
estimate jointly with the rectangle square and original variance debts.
The finite-cutoff kernel analysis shows why a stand-alone Gram sign or
endpoint majorant cannot supply that estimate. All hard RP gaps remain
open; goal active, no external blocker.

## Search and process audit

Three documented deep searches, budget 300 seconds each, all completed
with partial=false, errors=[], no unfinished stages and zero pending
inventory files:

- Reciprocal cutoff: query 1215652; coverage 1215665/current 1215671;
  65017 files.
- Native cross/debt kernel: query 1215672; coverage/current 1215688;
  65021 files.
- Product Riesz kernel: query 1215710; coverage 1215718/current 1215729;
  65024 files.

All reported unavailable/unmeasured semantic coverage and incomplete
background refresh; first and third also reported older snapshots.
Compiler coverage was mostly pending/stale. Candidate lemmas, source
arguments, proof ideas and ingredient sets were inspected as source-only
leads, not fresh certificates. RH-dependent Chebyshev bounds are unusable
as unconditional producers. The suggested Bessel debt and D4BM cutoff
bounds concern other carriers. The corpus's second-grade Riesz mass uses
sqrt(M)-sqrt(n), which differs from this trial's W_N(n); they were not
silently identified. The exact Selberg coefficient identity and relevant
finite product/ratio source definitions were read directly.

Owned searches 81333, 71048 and 23793 all exited zero. Their temporary
JSON results were removed after this record. No owned process remains.
No Lean file changed, so no leaf/umbrella build or fresh axiom audit was
run. Global lint was not repeated. No new axiom, numerical experiment,
subagent, resource-limit override, commit or push was used.
