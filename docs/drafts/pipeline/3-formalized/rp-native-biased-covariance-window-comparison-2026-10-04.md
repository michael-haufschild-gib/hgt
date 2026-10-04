# RP-66: native biased covariance has no additional critical norm debt

Route RP. Native finite-window comparison formalized in Lean below.
This proves a uniform comparison, not a finite global energy bound.
Positive-damping negative work, signed high-LCM control, and both
history debts remain open.

## Comparison statement

Let U be the corpus's divisorContinuousUnitHead. For real x>0 put
A_x(d)=sqrt(d)*U(x/d), and put theta_p=1-1/p. Let theta(d) be its
squarefree multiplicative extension. Define the native biased mean

    H_theta(x)=sum_(1<=d<=x) mu(d)*theta(d)*A_x(d)

and the complete biased pair covariance

    E_theta(x)=sum_(1<=d,e<=x) mu(d)*mu(e)*A_x(d)*A_x(e)
      *theta(rad(d) symmetricDifference rad(e)).

Non-squarefree indices have zero coefficient. Both sums are finite;
A_x(d)=0 when d>=x. Write H for the unweighted native full head.
There exist absolute constants C>=1 and K>=1 such that, for every
epsilon>=0 and T>=0, with

    J_(epsilon,T)(F)=integral_0^T exp(-epsilon*t)*F(t)^2 dt,
    h_theta(t)=exp(-t)*H_theta(exp t),
    h(t)=exp(-t)*H(exp t),
    V_(epsilon,T)=integral_0^T exp(-(2+epsilon)*t)*E_theta(exp t) dt,

the following inequalities hold without any global admission premise:

    J(h_theta) <= V <= C*J(h_theta),
    K^(-2)*J(h) <= J(h_theta) <= K^2*J(h).

Consequently K^(-2)*J(h) <= V <= C*K^2*J(h).
The constants do not depend on damping, terminal cutoff, or prime core.

This pays the additional covariance/prime-deletion cost relative to
the literal native head. It does not bound J(h) as T grows. In
particular it cannot be advertised as payment of negative native work.

## 1. Fixed-window causal norms, with every endpoint retained

Fix a finite prime set P for the moment. All heads below are finite
linear combinations of U(x/d), so are continuous, vanish for x<=1,
and have finite square integrals on every finite log window.
Continuity follows directly from the corpus's global Lipschitz bound.

Put u(t)=exp(-t)*U(exp t) and

    D_p f(t)=p^(-1/2)*f(t-log p).

For a causal f (zero at t<=0), change variables on the finite interval:

    ||D_p f||_(epsilon,T)^2
      =p^(-1-epsilon)*integral_0^(max(T-log p,0))
           exp(-epsilon*s)*f(s)^2 ds
      <=p^(-1-epsilon)*||f||_(epsilon,T)^2.

Here ||f||_(epsilon,T)=sqrt(J_(epsilon,T)(f)). The ordinary L2
triangle inequality applies on this finite weighted measure space.
All D_p commute. Causality makes every geometric inverse finite
on the chosen window: D_p^m f is identically zero there once
m*log p>=T. Thus the identity

    (I-theta_p*D_p)^(-1)=sum_(m>=0)theta_p^m*D_p^m

means a finite sum on the window, not an assumed full-ray inverse.
Its norm is at most (1-theta_p/sqrt(p))^(-1); nonnegative damping
can only improve this bound.

## 2. Simultaneous cofactor recovery retains the causal gain

Let h_(theta,P)=product_(p in P)(I-theta_p*D_p)u.
The exact finite divisor expansion from RP-63/RP-65 gives

    exp(-2*t)*E_(theta,P)(exp t)
      =sum_(r|product P) gamma(r)/r
          *h_(theta,P\primeFactors(r))(t-log r)^2,
    gamma(r)=product_(p|r)(1-theta_p^2).

In particular the r=1 term is h_(theta,P)^2. For every r in this
sum, recover the deleted head by the commuting finite geometric
inverses from section 1. Translation by log r contributes
r^(-epsilon) after squaring. Hence

    V_(epsilon,T,P) <= J(h_(theta,P))*
      sum_(r|product P) gamma(r)/r *
        product_(p|r)(1-theta_p/sqrt(p))^(-2)
      =J(h_(theta,P))*
        product_(p in P)[1+(1-theta_p^2)/
          (p*(1-theta_p/sqrt(p))^2)].

This differs from the sharp pointwise cofactor Cauchy estimate:
the norm of the causal dilation supplies 1/sqrt(p), so its recovery
cost does not cancel gamma(r).

Let d0=1-1/sqrt(2)>0. Since p>=2,

    1-theta_p/sqrt(p)>=d0,
    1-theta_p^2=2/p-1/p^2<=2/p.

Using 1+v<=exp(v) for v>=0 and the convergent positive integer
inverse-square series, every finite product is bounded by

    C=exp((2/d0^2)*sum_(n>=2)n^(-2))<infinity.

This proves both covariance inequalities for every finite P, with
one C. No estimate of the native head was assumed.

## 3. Bias and the original native head are uniformly comparable

Let h_P=product_(p in P)(I-D_p)u. The exact commuting identities are

    (I-theta_p*D_p)*(I-D_p)^(-1)
      =I+(1-theta_p)*D_p*(I-D_p)^(-1),
    (I-D_p)*(I-theta_p*D_p)^(-1)
      =I-(1-theta_p)*D_p*(I-theta_p*D_p)^(-1).

Again every inverse is a finite causal geometric sum on the window.
Both operator norms are at most

    1+1/[p*(sqrt(p)-1)] <= 1+d0^(-1)*p^(-3/2).

The finite product of these bounds is at most

    K=exp(d0^(-1)*sum_(n>=2)n^(-3/2))<infinity.

Applying the first product to h_P and the second to h_(theta,P)
gives ||h_(theta,P)||<=K*||h_P|| and its reverse. Square them.
No pointwise sign of any head or correlation is used.

## 4. Exact native moving-cutoff specialization

For each fixed T choose P containing every prime <=exp(T). At every
t<=T, any omitted divisor is >exp(t), so its unit source channel is
exactly zero. Therefore h_P=h, h_(theta,P)=h_theta, and
E_(theta,P)=E_theta throughout the complete integration window.
This is finite-window equality, not a full-ray fixed-core limit.
The constants C,K are uniform in P; substitute these equalities
into sections 2 and 3. This proves the stated native comparison.

## Formalization construction

The Lean construction proves finite-window causal delay contraction
and recovery, the exact cofactor-square and signed-pair identity,
uniform summation of the cofactor costs, reversible bias transfer,
and exact native completion on the original integration window.
It audits the resulting native capstones and the individual literal
Möbius divisor channels, rather than only an abstract norm receiver.

A shorter finite induction can replace explicit smooth-number inverses.
For arbitrary continuous causal u, write L_p=I-theta_p*D_p,
H_P=product L_p, and let V_P(u) be the integrated divisor-square
covariance. Finite powerset splitting and commutation give

    V_(P union {p})(u)=V_P(L_p u)+gamma_p*V_P(D_p u).

The induction hypothesis bounds this by
C_P*(||H_(P union {p})u||^2+gamma_p*||D_p H_P u||^2).
The causal recovery inequality

    (1-q)^2*integral f^2 <= integral(f-q*f(.-a))^2

with q=theta_p/sqrt(p), a=log(p), and the shift contraction pay the
second term with exactly the Euler factor of section 2. For that
recovery inequality the pointwise certificate is

    (f-q*g)^2+q*(1-q)*g^2-(1-q)*f^2=q*(f-g)^2>=0.

Integrate and use integral g^2<=integral f^2. Nonnegative damping
can be absorbed into f and decreases q further. This proof needs
no full-ray Neumann-series construction or imported global admission.
The bias comparison can likewise use weighted Young inequalities
and this recovery bound, avoiding unnecessary Hilbert-space infrastructure.

Do not claim global square admission. The native zero-damping
nonintegrability from RP-50 remains consistent and transfers to V;
positive-damping admission is still the substantive RH frontier.

## Corpus/novelty audit

The direct prime-deletion deep search returned the exact natural
cutoff interpolation law in MobiusDivisorCoprimeHeadDeletion,
the continuous delay law in MobiusDivisorCriticalClockProductTransport,
and coprime floor inversion in MobiusDivisorCoprimeColumnTransport.
Their source statements were inspected; no retrieved result supplied
this uniform biased covariance/native-window comparison.
An exhaustive source-text search for cofactor norm, biased covariance,
and covariance/mean bounds found no matching comparison theorem.
This is not a claim of global literature novelty.

Search generation 1220773, coverage 1220804/current 1220805,
65077 files. Partial=true: semantic_retrieval's Qdrant request timed
out; available candidates/source arguments/ingredients were used.
Semantic coverage unmeasured; refresh incomplete; most compiler
states pending, stale, or unavailable. Lean verification remains pending.

## Lean result and audit

All names below are in `RHTower.RoutePWindow`.

- `native_signed_pair_comparison` in `RoutePNativeSignedPairComparison.lean`
  compares the complete native signed-pair covariance with the original
  `mobiusDivisorFullHead` energy, in both directions.
- `native_covariance_mean_comparison` in `RoutePNativeBiasedMeanComparison.lean`
  proves J(h_theta)<=V<=C J(h_theta).
- `native_bias_comparison` in that same leaf proves
  J(h)<=B J(h_theta) and J(h_theta)<=B J(h), with one absolute energy
  factor B. Thus B is the square of the norm factor K in the paper.
- `nativePrimeChannel_eq_divisor` in `RoutePNativePrimeChannelDivisor.lean`
  identifies each individual prime-subset channel, with d its product,
  as mu(d)*sqrt(d)*U(exp(t)/d)/exp(t).
- `sum_nativePrimeChannel` identifies the complete channel sum with the
  original full native head, and `nativePrimeChannel_zero` retains exact
  physical clipping. `nativeCofactorCovariance_eq_signedPair` proves the
  complete symmetric-difference covariance identity.

Lean represents the covariance by prime-subset labels, with every
individual divisor coefficient identified. A separate syntactic
reindexing theorem into a double natural-number sum is not exported.
The native head on the comparison's other side is the original corpus
definition, not a newly assumed source or a fixed-core full-ray limit.

The two earlier causal-helper theorems and all 56 public theorems in
the 12 new leaves passed `/tmp` axiom audits with exactly propext,
Classical.choice, Quot.sound. Every leaf passed its foreground final
`lake --old env lean` audit with explicit olean output and no diagnostics.
All leaves are wired into RHTower; no umbrella or full build ran.
No heartbeat override, numerical experiment, subagent, or added axiom.

Final global formal lint still fails on the same 12 unrelated unreachable
modules recorded in RP-63; none names these leaves. An intermediate lint
also saw ThetaCuspC5IntrinsicClockGerm, which was absent from the final
lint errors. The scoped whitespace check passed.

### Direct square-energy proof of reversible bias transfer

The implementation replaces inverse operators by a finite induction.
Write E(f)=integral_0^T f^2 and g(t)=f(t-a). For 0<=c<=b<=3/4,
causal recovery gives E(g)<=16 E(f-bg), and likewise for c.
Set d=b-c in [0,1]. The exact two Young certificates are

    (1+d)(x^2+d y^2)-(x+d y)^2=d(x-y)^2,
    (1+d)(x^2+d y^2)-(x-d y)^2=d(x+y)^2.

Integration and recovery bound both perturbations by
(1+d)(1+16d)E(k)<=(1+33d)E(k). Thus E(f-bg) and E(f-cg)
compare in both directions with factor 1+33(b-c). Commuting finite
differences permit prime-set induction without any infinite inverse.
For b=q_p, c=(1-1/p)q_p, 0<=q_p<=1/sqrt(p), the gain difference
is q_p/p<=p^(-3/2). The product is at most
exp(33 sum_{n>=1} n^(-3/2)), uniformly in damping and prime set.
This is a proof of the transfer itself, not a norm-admission premise.

The proof now includes native source identification, complete signed-pair
expansion, and exact window completion. It closes the relative covariance
cost, not the absolute positive-damping source-energy estimate. Negative
work at each positive damping, signed high-LCM control, both history debts,
and the unconditional RH goal remain open.

Further corpus checks: finite-covariance deep search generation 1221006;
bias-transfer search generation 1221242; signed-pair search generation
1221378. All returned partial=false and no errors, with available
candidate/source/idea/ingredient fields inspected. The last coverage was
65121 files, zero pending/inventory errors, snapshot 1221385/current
1221386. Semantic coverage was unmeasured and background refresh incomplete;
compiler freshness was mostly pending/stale/unavailable. No retrieved
argument supplied the native comparison. Two ArithmeticFunction-filtered
lexical queries returned zero hits without freshness metadata; exact
installed source and a passing `/tmp` API audit verified the multiplicative
Möbius product and square-root identities actually used.
