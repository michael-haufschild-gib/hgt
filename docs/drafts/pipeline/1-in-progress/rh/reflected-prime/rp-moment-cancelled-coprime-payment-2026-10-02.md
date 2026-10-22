# RP-46: moment-cancelled coprime payment

Status: conjecture under paper audit; no new Lean theorem.
Goal: the unconditional signed RP history floor, without changing its debts.

The completed high-LCM absolute budget is now excluded by RP-45. The
candidate here keeps signed coprime work and the finite physical boundary.
Let u(t)=exp(-t/2)*H(exp t), with H the literal full Mobius divisor head,
and let v be its unit-head dilation source as in RP-44. The proposed
mechanism is a finite-history completion that cancels the Mellin moment at
the pole, followed by a source-specific energy estimate. No infinite
critical L2 admission is assumed.

First obligation: verify the exact native zero-moment statement in the
corpus, including the bridge from the full head to criticalContinuousAbel.
Second: retain every term introduced by completing a finite history.
Third, the hard step: prove a uniform bound for the actual native square
from the completed signed form. Positivity of a form or an admitted source
norm is insufficient without an estimate controlling the native square.
Any frequency argument must justify its literal source domain; analytic
continuation of a signed transform does not admit a positive square moment.

The prior full-row attempt has a precise unpaid term. For q the centered
Mobius reconstruction and r its dilation source, write q_a=q(T-log a).
Then sum_a q_a=r(T). Splitting the coprime form into its endpoint, the two
endpoint cross slots, and the bulk gives

    CE(q,T)=2*q(T)*r(T)-q(T)^2+bulk(q,T).

Thus estimates for complete nontrivial rows cannot silently bound the bulk
after removing index1: doing so restores q(T)^2. For the CCM centered
carrier, its explicit Mobius work must also be retained before transferring
to the complete prime deficit. This is a paper diagnosis, not a new theorem
or a claimed payment. The CCM row source is not identified with RP-44's u.

Search and proof-attempt outcomes are recorded in the main RP-46 working
log. No generic identity-only leaf will be added as a substitute for the
uniform signed estimate.

## Sharp cost exposed by the completion attempt (paper)

Use the critical Abel profile for this calculation; its zero boundary mass
is already proved in MobiusDivisorCriticalAbelSignedBoundaryMoments. The
all-real bridge to the RP-44 full-head definition is not silently assumed.
Put R(T)=integral_0^T exp(-t)*u(t) dt. If a completion g agrees with u on
[0,T] and cancels the total exp(-t) moment, its tail must have moment -R(T).
For0<epsilon<1, weighted Cauchy--Schwarz gives

    integral_T^infinity exp(-(1+epsilon)*t)*g(t)^2 dt
      >= (1-epsilon)*exp((1-epsilon)*T)*R(T)^2.

The equality profile is

    g(t)=-(1-epsilon)*R(T)*exp((1-epsilon)*T)*exp(epsilon*t), t>T.

Both its weighted square integral and moment are admitted because
1-epsilon>0. Thus the displayed cost is sharp. This is a paper minimization
calculation, not a claim that a uniformly bounded native completion exists.
The existing zero-moment identity alone says nothing about the size of this
cost. PNT logarithmic savings do not supply its critical exponential bound.

For c(n)=Lambda(n)-1+2*gamma*1_{n=1}, with n>=1, the read cumulative
identity gives psiDefect. The read square-root summatory integral therefore
gives H(x)=sum_{1<=n<=x}c(n)*(sqrt(x)-sqrt(n)). For N=exp(T), direct finite
integration gives

    R(log N)=F_N(1)/3-P_N/N+(2/3)*Q_N/N^(3/2),
    F_N(1)=sum_{n<=N}c(n)/n,
    P_N=sum_{n<=N}c(n), Q_N=sum_{n<=N}sqrt(n)*c(n).

Each summand's integral from n to N is
(1/3)/n-1/N+(2/3)*sqrt(n)/N^(3/2). No endpoint is discarded. The
combination above, not its separately estimated summands, would have to
pay the sharp completion cost. The same P_N,Q_N occur in the earlier
finite-source terminal quadratic; F_N(1) is an additional retained moment.
The candidate has not produced the required signed estimate and is not a
proved no-go against the native source. No generic minimization wrapper is
being substituted for the hard arithmetic bound.

## Domain check

VisibleCoprimeMellinSymbol proves the zeta quotient with both real parts
greater than1. VisibleCoprimeMellinSummability proves this is exactly the
ordinary unconditional summability domain of that full family. On the
candidate critical line sigma=(1+epsilon)/2, epsilon<1, the quotient is
therefore only a proposed continuation for the completed calculation until
an ordered-source admission theorem is supplied. Its formally nonnegative
factor |zeta(sigma+i*t)|^2 would in any event not provide a lower bound for
native energy without an additional source-specific estimate. No division
by an unproved nonzero zeta value is used.

## Arithmetic parent test

RouteEAllQuotientEdgeDominance has an actual nonpositive signed section,
but its pairs are(d,qd) and(2d,qd) with a different Gamma--Hankel weight.
The comparable pair(d,qd) is in RP's already-paid low-LCM sector whenever
it is active. The second edge and its two-edge weight have not been
identified with the RP kernel, so their sign is not transferred.
The current attempt needs cancellation across incomplete, noncomparable
cofactor pairs and the physical terminal boundary. An integer-quotient sign
alone does not supply it.

No critical estimate or new formal theorem resulted from these attempts.
The next precise quantity to attack is the full boundary combination
F_N(1)/3-P_N/N+(2/3)*Q_N/N^(3/2), together with the signed interior work.
Bounding that combination separately may be stronger than necessary; the
original joint terminal compensation remains the target.

## RP-47: joint completion and chronological work tests

The elementary joint completion calculation does not supply cancellation.
Write a=(1-epsilon)/2, r(T)=exp(a*T)*R(T), and
f(T)=exp(-(1+epsilon)*T/2)*u(T). Then r'=a*r+f and r(0)=0.
On every finite interval, integration by parts gives

    integral_0^T f^2 = integral_0^T (r'^2+a^2*r^2)-a*r(T)^2.

The sharp completion cost is 2*a*r(T)^2. Adding it therefore leaves
the positive terminal term +a*r(T)^2, not a cancellation or an upper
energy estimate. This finite calculation neither retires the native
moment-constrained candidate nor warrants a generic identity-only leaf.

The actual normalized variance flux was read in
CCMActualHeadMatchedQuantileParabolicNormalizedVarianceFlow. It is
-w*m/m_next*(2*offset*displacement+displacement^2). The previously proved
eventual orientation opposes displacement; it does not control the signed
sum of admissions. The anchor graph bound likewise leaves its terminal
mass-offset channel and the second debt unpaid.

CCMPrimeDeficitChronologicalWork gives a separate exact source balance:
positive causal storage plus integrated critical deficit energy equals
2+2*chronological work+prime-entry jump budget. The jump budget is already
quadratic in logarithmic time. Positivity bounds work from below; the
needed estimate is an upper bound. Its arithmetic term is precisely

    sum_{n<=N} Lambda(n)/n *
      [D(log n)+2*(n-psi(n)+Lambda(n))],

sampled before the prime-power jump. Both terms and the self-jump remain.
SelbergSymmetryCore controls psiDefect(N)*log N plus the product convolution
sum Lambda(k)*psiDefect(floor(N/k)), with error O(N). It supplies neither
the opposite-twist quadratic correlation nor the required upper bound on
chronological work. No change of carrier or inequality direction is used.

These tests have not proved a new native critical estimate. The next
attempt keeps the complete prime-insertion mixed correlation and the
physical clock boundary together; separate diagonal absorption was already
known and is not being counted as progress.
