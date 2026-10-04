# MC scaled Liouville density cone

- **ID:** MC-C12.93
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; paper proof OPEN, Lean OPEN.
- **Source:** C12.91 finite-prime insertion; C12.92 actual scalar square-root obstruction; corpus `LiouvilleDirichletSeries`, `LiouvilleDyadicGramLaw`, and `LiouvillePrimeBandAlgebra`.

## Exact hard target

For every finite set P of primes, let J_P(t) be the full sum of lambda(n)*exp(-n*t)/n over P-smooth positive integers. Conjecture: K_P(t)=J_P(t)-t*J_P'(t)>=0 for every t>0. All powers of every selected prime are retained. This is an arithmetic sign conjecture, not a bound supplied as a hypothesis.

If proved, (J_P(t)/t)'=-K_P(t)/t^2<=0 and its limit at infinity is zero, so J_P>=0. Dominated convergence under prime exhaustion would then give the literal full J_lambda>=0 and hence the established one-sided MC target. The RH-producing gap is still J_lambda(t)>=-C_epsilon*t^(1/2-epsilon); neither that bound nor this stronger sign has been obtained.

## Why this test differs from the failed induction

C12.91 shows J_P need not be decreasing even for two primes. K_P>=0 permits J_P'>0; no failed antitone premise is reused. Differentiating the absolutely convergent insertion identity gives exactly

    K_(P union {p})(t)=sum_(e>=0)(-1)^e/p^e * K_P(p^e*t).

Its sign requires actual cancellation. A sufficient pairing inequality is K_P(t)>=K_P(p*t)/p for every new prime p; this is another unproved arithmetic obligation, not an automatic consequence of K_P>=0. Iterating derivative cones without proving closure merely creates a hierarchy and is not progress.

## Corpus audit underway (2026-10-04, 1005i)

The first broad deep search returned ordinary probability exponential densities and unrelated dilation maps; they do not apply. The more focused Liouville/nonnegative search returned nonnegative WKB weights, theta atoms, and cofinal additive-correlation positivity. None states this physical density sign. In particular `LiouvilleEvenIndexPositiveRecurrence` supplies cofinal signs of additive correlations, not an all-t sign of J_P or K_P. The literal coefficient identities and complete summability/prime-power decomposition are the relevant corpus inputs. The focused derivative/insertion search completed; it supplies prime-power identities and exact cofactor residuals, not the missing sign. No numerical experiment, new axiom, conditional RH theorem, or formal result is claimed.

## First proof attempt: retain the complete square-cofactor average

The insertion identity gives the exact paired expression

    K_(P union {p})(t)
      = sum_(j>=0) p^(-2j) * (K_P(p^(2j)*t)-K_P(p^(2j+1)*t)/p).

Positivity of K_P alone does not determine these differences. Attempting to prove that K_P/t is decreasing introduces (1-t*d/dt)^2 J_P, then higher orders. No closed cone has been proved; relabeling this hierarchy is not a sign argument.

The literal coefficient identity lambda=mu*squareIndicator gives a more precise full-source form. Put Q=product P and

    k_P(u)=sum_(d|Q) mu(d)/d * (1+d*u)*exp(-d*u).

Then, with every P-smooth square cofactor retained,

    K_P(t)=sum_(m P-smooth) k_P(m^2*t)/m^2.

Indeed each integer in the smooth monoid has the unique parity factorization n=d*m^2 with d squarefree, and lambda(n)=mu(d). The finite sum over d and full exponentially convergent cofactor sum may be interchanged. This is a paper identity, not a formalized sign theorem. Termwise nonnegativity of k_P is a stronger auxiliary claim and is not assumed. The hard question is the sign of this whole square-cofactor average uniformly over P.

The corpus's `LiouvilleDyadicGramLaw` was read: it proves a positive quadratic expression for an even additive correlation and an alternating odd-seed orbit. It does not identify J_P or K_P with that quadratic expression. `MobiusLaplaceLandauOscillation` was also read at its definitions and theorem statements: it treats the unweighted Mobius Laplace source and its subcritical power comparisons. Its oscillation cannot be asserted for k_P or the harmonic primitive without an additional transfer. No such transfer is claimed.

**Search audit.** Four further searches (broad positive source; literal sign; scaled cone; finite Euler sign) completed. First partial=true, other three partial=false. Snapshots65129/65131/65134/65136 files, compiled43, pending49119/49120/49123/49123, stale2660; generations1221508/1221539/1221574/1221594. All reported semantic coverage unavailable and background refresh; last three also older-generation warnings. All candidates, source arguments, proof ideas and ingredient sets inspected. Generated probability-density positivity, WKB Liouville weights, prime-window derivative and algebraic prime-localization chains have different sources and were not used. The finite Euler ingredient incorrectly proposes zero at every positive prime exponent; the actual moebius prime-power theorem gives -1 at exponent1. No failed generated premise is accepted.

**Checkpoint.** No proof or falsification of the K_P sign, no new critical estimate, and no new Lean module for this candidate. The next attack must prove a sign/cancellation law for the complete square-cofactor average, or derive a genuine arithmetic counterexample and its positive survivor. No optimization of constants or additional conditional receiver is needed.

## Active attack (2026-10-04, 1005j)

Previous turn classified as verified progress: C12.92 actual simple-zero survivor and all-small-t no-square result are audited. This turn attacks the complete K_P sign. No improvement of the critical lower bound is assumed. Current sources and frontier map checked; square-cofactor and real multiplicative positivity searches in progress. A finite-prime induction must preserve the actual source, not posit a generic positivity cone.

## 1005j paper deductions: positive deletion and exact discrepancy work

The deductions in this section are PAPER, not new Lean declarations. No critical bound or sign theorem has been proved.

### Finite-prime positivity is equivalent to the full-source sign

Let b_P(d) be1 exactly when d is squarefree and all its prime factors lie outside P. Its local factor is1+z outside P and1 inside P. Since the literal Liouville factor is1/(1+z), coefficientwise

    lambda*b_P = lambda*1_(P-smooth).

Consequently, for t>0,

    J_P(t)=sum_d b_P(d)*J_lambda(d*t)/d,
    K_P(t)=sum_d b_P(d)*K_lambda(d*t)/d.

These are absolutely convergent full identities: after expanding, each n receives at most its number of divisors, and that number is at most n. The absolute double sums are bounded by sum_n exp(-nt) and sum_n(1+nt)exp(-nt), respectively. Thus a nonnegative full K implies every finite-prime K_P is nonnegative. Conversely, exhaust the primes; the coefficients converge pointwise to lambda and the same exponential majorant gives K_P(t)->K_lambda(t). The proposed finite-prime sign is therefore equivalent to the full K sign, not a weaker positivity problem. This does not invalidate induction, but no finite-prime positivity premise may be imported as already established.

For P empty the exact inverse is particularly simple: lambda*mu^2=delta. This follows at each prime power from (-1)^e+(-1)^(e-1)=0 for e>=1. Therefore

    sum_(n>=1) mu(n)^2*K_lambda(n*t)/n = phi(t),
    phi(t)=(1+t)*exp(-t).

The pointwise product lambda*mu^2 in the squarefree-half source is different from this Dirichlet convolution; the retrieved pmul theorem is not substituted for the inverse identity.

### The continuum contribution is positive; the complete correction is signed

Put A(x)=sum_(n<=x)mu(n)^2, rho=6/pi^2, E(x)=A(x)-rho*x for x>=1, and K=K_lambda. The inspected `SquarefreeCountingAsymptotic.abs_sum_moebius_sq_sub_le` gives the full integer-cutoff square-root count error. The short-interval theorem in `Sieve/SquarefreeCount` initially concerns a truncated divisor sum; its full-count specialization requires covering every square divisor and is not assumed for arbitrary short intervals.

Abel summation of the exact squarefree inverse, with the full endpoint retained, gives

    phi(t)=rho*K(t)+rho*integral_t^infinity K(v)/v dv+R(t),
    R(t)=integral_1^infinity E(x)/x^2 * (K(t*x)-t*x*K'(t*x)) dx.

For fixed t>0 all integrals converge absolutely: K and its derivatives have exponentially decaying full coefficient series at infinity, and the lower endpoint is positive. On functions with this decay define Hf(t)=t*integral_t^infinity f(u)/u^2 du. Direct integration shows

    H[(1-u*d/du)K](t)=K(t),
    (Id-H)phi(t)=t*exp(-t).

Fubini is valid in the R integral by the same exponential majorants. Applying Id-H therefore yields the exact source equation

    rho*K(t)=t*exp(-t)+t*C(t),
    C(t)=integral_1^infinity E(x)*K'(t*x)/x dx.                 (SC)

The positive continuum contribution has been solved explicitly. The remaining term is the actual squarefree-discrepancy/Liouville-derivative correlation. Dropping E or replacing it by its density would erase this entire term.

The weaker sufficient RH target is C(t)>=-C_epsilon*t^(-1/2-epsilon) near zero for every epsilon>0 (restrict0<epsilon<1/2). Equation(SC) then bounds K below by a constant times -t^(1/2-epsilon). Since

    J_lambda(t)=t*integral_t^infinity K(u)/u^2 du,

the same lower power transfers to J_lambda, with the complete large-u tail contributing only O(t). This keeps the original critical target and avoids requiring an everywhere positive K. No such correlation estimate has been proved.

### What the absolute count bound fails to settle

The known |E(x)|<=C*sqrt(x) gives only

    |t*C(t)| <= C*sqrt(t)*integral_t^infinity |K'(v)|/sqrt(v) dv.

The integral contains the unknown source derivative near zero. An unconditional logarithmic bound for K' would return only logarithmic control after integration, not the half-power estimate. Assuming its critical weighted integrability would assume a new hard input. Improving a numerical constant does not discharge that input.

For a power mode K(t)=t^alpha, the formal scalar multiplier is

    q(alpha)=(alpha/rho)*integral_1^infinity E(x)*x^(alpha-2) dx.

For0<alpha<1/2 this integral is absolutely convergent by the existing square-root count error. The Mellin identity of the squarefree series gives

    q(alpha)=1+alpha/(rho*(1-alpha))*zeta(1-alpha)/zeta(2-2alpha).

This scalar identity does not bound the action on the actual K. The critical limit suggests mass1 atalpha=1/2; using an ordinary integral there requires an endpoint convergence proof, so no critical absolute contraction theorem is asserted. A possible proof of endpoint integrability splits the exact mu-square count at R=sqrt(X)/log^B(X), bounds the short fractional-part sum by R, and uses the corpus's arbitrary fixed-log Mertens estimates for the remaining grouped sums. This is a dependency to audit, not a replacement for the required signed correlation estimate.

### Completion must retain the lower-scale boundary

Extending E to0<x<1 by E(x)=-rho*x introduces the missing boundary explicitly. If K(0+)=0 and the required absolute derivative integrals are justified from fixed-log source estimates, then

    integral_0^1 E(x)*K'(t*x)/x dx = -rho*K(t)/t.

Thus (SC) makes the completed integral equal -exp(-t), while its x>=1 part still contains rho*K(t)/t. Reindexing E through the full mu-square divisor identity can produce a completed sawtooth identity; it cannot remove this lower-scale boundary or prove K's sign. No use of that completion as a cancellation bound is permitted by this derivation.

**Assessment.** The finite-prime sign was neither proved nor falsified. The positive-deletion equivalence and equation(SC) are new paper deductions from the actual coefficient source, with every summation and endpoint specified. They identify the unresolved collective work more precisely; they are not a new critical estimate. Next work should attack the lower bound for the actual C(t), retaining E and K' together. Do not formalize another conditional receiver or optimize the squarefree-count constant instead.

### Scalar dissipation does not give absolute contraction

Continuation of1005j; PAPER / Lean OPEN. This tests the proposed comparison step, not the sign conjecture or route MC itself. The positive-deletion coefficient argument already appears for H_lambda in C12.79 of the main card; its application to K here is not a new arithmetic cancellation theorem.

For0<alpha<1/2 define the signed and absolute comparison multipliers

    q(alpha) = alpha/rho * integral_1^infinity E(x)*x^(alpha-2) dx,
    a(alpha) = alpha/rho * integral_1^infinity |E(x)|*x^(alpha-2) dx.

Both integrals converge by the inspected full square-root count bound. The squarefree Dirichlet identity, Abel summation and analytic continuation give

    1-q(alpha) = -alpha/[rho*(1-alpha)]
                 * zeta(1-alpha)/zeta(2-2alpha) > 0.

Here the numerator is negative on the real strip and the denominator is positive in absolute convergence. Moreover q(alpha)->1 as alpha increases to1/2: the numerator has a finite limit and the denominator has the actual pole at1. This is an Abelian limit of SUBCRITICAL integrals. It does not assert convergence of the ordinary endpoint integral mentioned above.

The absolute comparison has a different limit behavior. Since1/2<rho<1, the interval(1/rho,2) is nonempty and A(x)=1 there, so E(x)=1-rho*x<0. Choose any closed nondegenerate interval[u,v] strictly inside it. Then

    a(alpha)-q(alpha)
      >= 2*alpha/rho * integral_u^v (rho*x-1)*x^(alpha-2) dx.

The right side has a strictly positive limit as alpha increases to1/2. Therefore a(alpha)>1 throughout some left neighborhood of1/2. This excludes the particular absolute derivative-envelope contraction argument near the required exponent. It is not a lower bound on the norm of every possible function-space operator, and does not exclude a signed, source-specific estimate. No mathematical computation or finite numerical example is used: the negative interval follows symbolically from the density and the first counting interval. The corpus provides the full squarefree density, `pi_sq_div_six_lt_two`, and `riemannZeta_real_strip_neg`; a new combined Lean theorem has not been built.

The positive statement exposed by this failed comparison is the exact real-mode deficit above, tending to zero at the critical exponent, together with the strictly positive cost of discarding the negative part. Its actual discrepancy-integral formalization remains OPEN; this is not a completed no-go or a retired candidate.

For complex alpha with0<Re(alpha)<1/2 the same analytic multiplier satisfies

    q(alpha)=1  iff  zeta(1-alpha)=0.

The denominator zeta(2-2alpha) is nonzero in absolute convergence. Thus checking only real modes cannot settle the potentially obstructing oscillatory modes. No uniform complex coercivity or bound for the actual C(t) was obtained. The hard next step remains a lower estimate for that signed correlation; treating the real gap as an operator bound would assume the missing result.

### 1005j search and verification ledger

Nine documented corpus searches completed, all partial=false. In order (square-cofactor, real-positivity, harmonic-oscillation, squarefree-inverse, squarefree-renewal, critical-renewal-moment, renewal-spectrum, critical-finite-part, discrepancy-mellin-api), snapshot file counts were65142/65143/65147/65148/65151/65153/65155/65155/65159 and compiler-pending counts49125/49126/49130/49131/49133/49134/49135/49135/49137. Every snapshot reported43 compiled snapshots,2660 stale entries, semantic coverage unavailable, older-generation warnings, no pending method invalidation, and background refresh. Snapshot/current generations:1221688/1221691,1221711/1221712,1221776/1221777,1221797/1221798,1221819/1221820,1221883/1221886,1221960/1221962,1221960/1221970,1222019/1222020.

Candidate statements, source arguments, proof ideas and ingredient sets inspected. Generated chains confusing pmul with convolution, arithmetic Liouville with a vortex theorem, critical fixed-origin discrepancy with normalized squarefree clock moments, and squarefree indicator with totient residue were rejected. Generic Mellin inversion retains its convergence hypotheses; a quarter-density count or a positive Schur kernel does not prove the signed correlation estimate. The finite-part search did not establish the ordinary critical discrepancy moment. One invalid rg character range was corrected; one guessed partial-summation filename was corrected by inventory to mathlib `NumberTheory/LSeries/SumCoeff.lean`. Neither failure affected source files.

No Lean source changed, no Lean build or axiom audit run, no new audited theorem, and no RH proof/falsification. No numerical mathematical experiment, added axiom, placeholder, heartbeat change, subagent, umbrella build or commit. The source sign and critical lower bound remain OPEN. This turn identified an exact retained correction and a failed comparison step; it did not improve the hard cancellation estimate. Temporary-output cleanup is recorded in the main working log after removal.

## Active signed-source attack (2026-10-04, 1005k)

Route MC, same actual C(t) target. Previous turn yielded paper evidence changing the next admissible action, not a critical estimate. Revalidated the current card. This turn tests whether complete multiplicativity can retain the sign lost by the absolute squarefree-discrepancy comparison. The dyadic Gram theorem is an identity for an additive quadratic channel, not for J or K; no transfer is presumed. Current signed-work and negative-part corpus searches are being audited before any new Lean code. No sign, coercivity or half-power conclusion at this checkpoint.

**Formal continuation.** The inspected `LiouvilleSignedCofactorDilation` keeps the full nondivisible-cofactor remainder; it does not supply its sign. The direct prime-deletion attempt therefore did not bound C(t). Closing the exact kernel obligation exposed by1005j instead: new `SquarefreeDiscrepancyMellin.lean` defines the literal real-cutoff count, discrepancy, restricted kernel and Mellin moment. It proves local integrability, half-plane holomorphy, the pole-cleared identity, the quotient formula and the exact complex unit-mode classification. The targeted leaf build and required direct `lake --old env lean` audit passed. The leaf is wired in RHTower; no umbrella build. The real-mode deficit, critical limit and absolute-comparison failure are being formalized next. No full C(t) bound or RH conclusion is claimed; the comparison no-go is not yet complete.


### 1005k completed exact-response audit

The paper comparison obligation above is now fully formalized. `SquarefreeDiscrepancyMellin`
and `SquarefreeDiscrepancyCriticalGap` prove the literal integral identity, complex unit-mode
classification, positive real-mode deficit, critical Abelian limit, uniform cost of absolute
values, and eventual absolute response greater than one. Dedicated proof/certificate:
`../3-formalized/mc-squarefree-discrepancy-response.md`. Only the absolute derivative-envelope
contraction is retired in `../5-failed/mc-squarefree-discrepancy-absolute-contraction.md`.
C12.93's actual finite-prime/full K sign remains OPEN.

Both targeted leaf builds and required direct audits passed; all23 public theorem axiom
checks standard-only. Imports wired, indexes regenerated, no umbrella build. Global lint
still has13 unrelated umbrella-reachability errors. Three documented corpus searches and
exact process correction are recorded in the survivor card.

**Assessment:** this closes the exact actual-kernel no-go with its strongest positive
survivor; it does not improve the critical signed C(t) estimate. The final energy search
returns source-specific cofactor identities, product-fibre identities and an RH-equivalent
energy bound, but no proof of their missing signed work. The generated squarefree-functional
chain incorrectly proposes vanishing without the functional's vanishing premise; it is not
used. The next conjecture must concern the actual signed source, not abstract operator
coercivity inferred from real q or an improved squarefree-count constant.

**Next retained-source test:** at a new negative record of t^(-a)K(t), subtract that same
power profile inside the full E/K' integral. The scalar profile has the now-proved deficit
1-q(a)>0. The remaining integral is the signed work of E against the derivative of the
actual profile difference; a record condition alone controls values, not this derivative
pairing. Conjecture: arithmetic prime-pairing of the full source controls this retained work
from below, uniformly over such records for every a<1/2. This is a proposed proof mechanism,
not a proved estimate or extra premise. Keep every nondivisible cofactor and boundary.
No generic maximum principle, endpoint integral convergence, or RH conclusion is asserted.


### Retained negative-record equation (1005k; paper diagnostic only)

For0<a<1/2, suppose t is a negative record of u^(-a)K(u) over u>=t, and put

    L_t(u)=K(u)-K(t)*(u/t)^a.

Then L_t(t)=0 and L_t(u)>=0 for u>=t. Subtracting the power mode in the full convergent
discrepancy integral gives exactly

    rho*(1-q(a))*K(t)
      = t*exp(-t)+t*integral_1^infinity E(x)*L_t'(t*x)/x dx.          (REC)

The integral converges absolutely: the actual K' decays exponentially at infinity and
the subtracted power is integrable against E(x)/x by a<1/2. The now-audited positive
factor1-q(a) is available; no bound for the rightmost signed work follows from its sign.

Stieltjes integration by parts makes the retained work a compensated sampling error:

    t*integral_1^infinity E(x)*L_t'(t*x)/x dx
      = limit_R [ integral_1^R A(x)*L_t(t*x)/x^2 dx
                  - sum_(1<=n<=R) mu(n)^2*L_t(t*n)/n ].

At the lower endpoint L_t(t)=0. The upper boundary E(R)*L_t(tR)/R tends to zero because
E=O(sqrt R), L_t(tR)=O(R^a), and a<1/2. The two displayed terms generally diverge
separately; their compensated difference is mandatory. Nonnegativity of L_t alone gives
no order comparison between its continuous and sampled readings. This is the same type
of actual sampling work retained earlier, now with the exact real power deficit isolated.

The attempted direct dyadic pairing uses

    K_odd(u)=K(u)+K(2u)/2,
    K_odd'(u)=K'(u)+K'(2u).

It retains the entire odd-cofactor source. The record inequality bounds values of
K(2u), not the signed derivative pairing, and does not prove the required lower bound.
This attempt therefore yields no critical estimate. Do not turn(REC) into a new conditional
RH receiver. The next hard obligation is a source-specific lower bound for this full
compensated work, using joint cofactor cancellation rather than scalar-mode signs.


## Active prime-logarithmic attack (2026-10-04,1005l)

Route MC; previous turn classified as progress because two exact actual-kernel leaves
were built and audited, but the RH-critical source estimate did not improve. Current task
is the full signed record work in(REC), not another scalar comparison or receiver. Recheck
the corpus's prime-logarithmic convolution identities before using them on the actual K.
Candidate mechanism: combine the log-coefficient identity with the negative-record profile
so that the prime and continuous logarithmic terms are compared jointly. Every even prime
power, nondivisible cofactor and boundary must remain. No sign or estimate is assumed.


### Full logarithmic identity and its retained cutoff (1005l)

**Paper derivation, no critical estimate.** C12.36 already contains the coefficient identity

    lambda(n)*log n = -(Lambda*lambda)(n)+2*(Lambda_square*lambda)(n),
    Lambda_square(m^2)=Lambda(m).

This is not newly claimed. Revalidated the actual complete multiplicativity and prime-power
values in `LiouvilleDirichletSeries`, and the divisor audit in
`LiouvillePrimeErrorDivisorAudit`. The latter explicitly returns weighted Liouville sums;
it supplies no independent prime-error cancellation.

For t>0 define

    H_K(t)=sum_(n>=1)lambda(n)*log(n)*(1/n+t)*exp(-nt),
    P_K(t)=sum_(d>=1)Lambda(d)/d*K(dt),
    Q_K(t)=sum_(m>=1)Lambda(m)/m^2*K(m^2*t).

All these full series converge absolutely for fixed t>0. Divisor regrouping gives
H_K+P_K=2Q_K. The exponential kernel supplies a useful joint physical form:

    H_K(t)=integral_0^infinity [exp(-v)*K(t)-K(t+v)]/v dv + J(t),

and hence

    integral_0^infinity [exp(-v)*K(t)-K(t+v)]/v dv
       +J(t)+P_K(t)=2Q_K(t).                                      (LOG)

Proof of the integral step: for n>=1,
(exp(-v)-exp(-nv))/v=integral_1^n exp(-a*v)da; Tonelli gives integral log(n).
The sum of absolute coefficient integrals is bounded by
sum_(n>=1)(1/n+t)*exp(-nt)*log(n)<infinity. Also
K(t+v)+v*J'(t+v)=sum lambda(n)*(1/n+t)*exp(-n(t+v)).
Finally -integral_0^infinity J'(t+v)dv=J(t), with the complete tail retained.
This proves(LOG) without assuming a critical source estimate.

The attempted negative-record substitution K(tx)=K(t)*x^a+L_t(tx) cannot split the two
infinite first-order terms separately. In the Frullani integral put x=1+v/t. The power
parts contain

    sum_(n<=R)Lambda(n)*n^(a-1) - integral_1^R x^(a-1)dx,

up to terms converging for a<1. If psi(x)=sum_(n<=x)Lambda(n) and D(x)=psi(x)-x,
finite Abel summation identifies this exact difference as

    1+R^(a-1)*D(R)+(1-a)*integral_1^R D(x)*x^(a-2)dx.               (PRIME)

For any a>0, a fixed-log majorant D(x)=O_B(x/log^B x) does not justify the limit in(PRIME):
the corresponding absolute integral has majorant x^(a-1)/log^B x, whose tail diverges.
This does NOT assert that the actual compensated limit fails to exist. It identifies an
unproved extra obligation; analytic continuation of a log derivative is not convergence
of this literal limit. The inspected von Mangoldt log-derivative theorems assume Re(s)>1.
Their generated search chain with log-times-harmonic decay does not discharge(PRIME).

In contrast, the squarefree E=O(sqrt x) used in(REC) admits the subcritical power subtraction.
Thus keep prime identities INSIDE a finite joint signed remainder. Removing the cutoff by
separate prime or continuous bounds would add the missing estimate. The even-prime-power
term remains summable at the chosen exponent, as C12.36 already records; it is not the gap.
No additional conditional receiver or logarithmic identity module was added.

### Real prime signs and a sum-of-squares test (1005l)

The audited single complex Dirichlet-square obstruction does not exclude sums of real
squares. Tested whether the literal weight w_t(n)=exp(-nt)/n can acquire positivity from
its restriction to completely multiplicative real signs. Such a construction would still
need an actual source estimate; the following exact comparison explains the obligation.

Let chi(p) be either1 or-1. Define a nonnegative multiplicative b_chi by

    b_chi(p^k)=2 if chi(p)=1 and k>=1,
    b_chi(p^k)=0 if chi(p)=-1 and k>=1,
    b_chi(1)=1.

Local series give chi=lambda*b_chi. For t>0 absolute divisor rearrangement is valid:
b_chi(d)<=number_of_divisors(d), and the full exponential product sum dominates all terms.
Consequently the complete real-sign evaluation obeys

    J_chi(t)=sum_(d>=1)b_chi(d)/d*J_lambda(dt).

Thus J_lambda>=0 everywhere implies positivity for every real sign character; the reverse
implication includes chi=lambda. This is the earlier positive-deletion mechanism with the
explicit nonnegative coefficients for real signs, not a new arithmetic cancellation law.
A square certificate would have to prove this actual positivity. It cannot be inferred
from the complex simple-zero theorem in either direction.

The proposed generic heat-positivity justification also fails as a general kernel argument.
For two distinct primes p,q, on the four squarefree labels1,p,q,pq let r(label)=label.
The coefficient of the nontrivial parity character in r is

    (1-p-q+pq)/4=(p-1)*(q-1)/4>0.

At t=0 the same Fourier coefficient of exp(-t*r) is zero and its derivative is strictly
negative. It is therefore negative for all sufficiently small positive t. Multiplication
by this damping does not generally preserve positivity of Fourier transforms on that
finite sign group. This is a symbolic derivative argument, not a numerical experiment.
It does NOT settle the actual initial coefficients1/n with every square and prime power
aggregated; that full input may behave differently. Generic positivity is not a substitute
for proving its particular arithmetic evolution. No no-go or source-positivity candidate
is retired on this paper diagnostic.

**Assessment.** Neither the negative-record/logarithmic test nor the real-square proposal
produced a half-power lower bound. The exact surviving problem is still the full signed
sampling work in(REC). Next attack must estimate it with its actual coefficient coupling;
keep finite prime cutoffs until their joint source remainder is bounded. Do not assume
ordinary convergence from a continued log derivative, use generic heat positivity, or
formalize another equivalence as an RH producer.

### 1005l search and execution ledger

Two documented deep searches reached terminal exit0, both partial=false. Queries:
`Liouville harmonic logarithmic derivative convolution von Mangoldt signed source`;
`completely multiplicative real sign exponential harmonic sum squares positivity`.
Files65191/65193, compiled43/stale2660, pending49159/49161. Snapshot/current generations
1222708/1222709 and1222735/1222735. Both report semantic coverage unavailable and background
refresh with no pending method invalidation; first also warns older snapshot generation.
Candidate and source-argument statements, proof_ideas and ingredient sets were inspected.
proof_ideas empty. The second generated chain tries to transfer a mean-square object through
a theorem requiring every exponential coefficient positive; the signed source does not
satisfy that premise. Generic convolution and Euler-product theorems retain summability.
The real-sign search's source identities and the existing complete-source declarations
were used only within their actual scope.

No Lean source changed, no build or new axiom audit run, no numerical mathematical
experiment, added axiom, placeholder, heartbeat increase, subagent, full/umbrella build or
commit. Previously audited leaves were not rechecked unchanged. No RH result or new critical
estimate. All new identities/diagnostics above are paper status; none is presented as a
kernel-checked theorem. Goal remains active and unmet.


## Active joint-product cutoff attack (2026-10-04,1005m)

Route MC. Previous turn made no critical-bound progress. Revalidated its retained cutoff
obligation and the actual corpus before proceeding. Current conjecture mechanism uses
the exact cancellation inside lambda*mu-square divisor fibres while retaining the whole
cutoff boundary. This is a different product grouping from Mobius-pair Gamma energy: the
proved constant-sign law for the latter must not be transferred to the former. The target
is still the full negative-record work, not a new identity or conditional receiver.


### Complete inverse fibres and the first cutoff band (1005m)

**Paper analysis; no critical source estimate.** The inspected
`MobiusProductFibreVariation.pair_sign` concerns mu(m)mu(n), whose nonzero product fibre
has fixed sign lambda(mn). The present inverse uses lambda(n/d)mu(d)^2 instead. Complete
multiplicativity and mu(d)=lambda(d)mu(d)^2 give

    sum_(d|n)mu(d)^2*lambda(n/d)
      =lambda(n)*sum_(d|n)mu(d)=1_(n=1).

Thus this full fibre really cancels. The retrieved pointwise-product lemma alone is not
the convolution statement; the complete divisor sum and its endpoint are necessary.

For integer R>=1 put

    c_R(n)=sum_(d|n,d<=R)mu(d)^2*lambda(n/d),
    S_R(t)=sum_(d<=R)mu(d)^2*K(dt)/d.

For fixed t>0 absolute rearrangement gives the exact full expansion

    S_R(t)=sum_(n>=1)c_R(n)*(1/n+t)*exp(-nt).

For1<=n<=R, c_R(n)=1_(n=1). ForR<n<=2R, every proper divisor of n is at most R,
so c_R(n)=-mu(n)^2. Therefore

    S_R(t)=(1+t)*exp(-t)
      -sum_(R<n<=2R)mu(n)^2*(1/n+t)*exp(-nt)
      +sum_(n>2R)c_R(n)*(1/n+t)*exp(-nt).                         (CUT)

The first boundary band has a fixed negative sign; the entire later boundary remains.
Removing the latter would not be a bound on the full signed source. The absolute divisor
majorant proves convergence at fixed t, but does not make the moving boundary negligible.
For any fixed c>0, at t=c/R the first band tends to the strictly positive quantity

    rho*integral_1^2 (1/u+c)*exp(-c*u)du.

This follows directly by Abel summation from A(x)=rho*x+O(sqrt x), with both band endpoints
retained. It is a symbolic limit, not a finite numerical example. It does not show that the
full boundary has this sign: later product bands can cancel it.

### The full moving tail retains the actual source profile (1005m)

Write T_R(t)=sum_(d>R)mu(d)^2*K(dt)/d and I(c)=integral_c^infinity K(u)/u du.
For fixed c>0 the complete Abel identity, applied to f_R(x)=K(cx/R)/x, is

    T_R(c/R)=rho*I(c)-E(R)*K(c)/R
      +integral_R^infinity E(x)*(K(cx/R)-(cx/R)*K'(cx/R))/x^2 dx.

The lower endpoint corresponds to d>R and uses A(R), not A(R-1). The upper boundary
vanishes by exponential decay. All integrals converge for this fixed positive c.
The square-root count bound gives

    T_R(c/R)=rho*I(c)+O_c(R^(-1/2)).                              (TAIL)

This keeps the entire signed K profile. Fixed-t exponential tail estimates cannot erase
rho*I(c) when the cutoff moves with t. The leading-term exponential estimate for K at
infinity makes I(c)>0 for all sufficiently large c, so even the full tail need not vanish
on these cofinal paths. Neither this fact nor the first-band sign controls the original
negative part near zero.

Trying to send c down to zero inside(TAIL) exposes the same missing source regularity.
The direct error bound contains

    sqrt(c/R) * [ |K(c)|/sqrt(c)
      +integral_c^infinity (|K(u)|+u*|K'(u)|)/u^(3/2) du ].

A uniform bounded-kernel estimate can bound this by O(R^(-1/2)), but it does not supply
I(0)-I(c)=O(c^(1/2-epsilon)). The latter is still a signed source estimate; recovering K
from its primitive requires additional control. A negative-record condition bounds values
K(dt) from below; the positive-weight head sum then gives the wrong direction for bounding
the negative record itself. No maximum-principle or inverse-order step has been proved.

The attempted cutoff recursion therefore has not improved the RH-producing bound.
Keep both the full signed moving profile and the head's compensated sampling error;
controlling only their absolute endpoints returns the unresolved work in(REC). No new
identity, tail lemma or receiver was formalized as a substitute for this hard estimate.
All(CUT)/(TAIL) statements above remain paper status, and no route or no-go is retired.

### 1005m source and execution ledger

Two documented deep searches reached terminal exit0, both partial=false:
`Liouville squarefree convolution product fibre signed discrepancy cancellation` and
`Liouville harmonic exponential positivity negative counterexample` (module Liouville).
Snapshots65197/65198 files, compiled43/stale2660, pending49164/49165;
generations1222847/1222849 and1222884/1222887. Both report older-generation and unavailable
semantic-coverage warnings, background refresh, no pending method invalidation. Candidate
and source-argument statements plus ingredient sets inspected; proof_ideas empty.
The product chain retains the missing complete divisor-sum step. The sign chain combines
logarithmic harmonic decay with a bound on an unrelated explicit exponential tail; it does
not produce an exponential or half-power decay rate for the Liouville source. Geometric
Liouville–Green and harmonic-function theorems refer to different objects.

Read the actual product-fibre sign law, complete multiplicativity, prime-power source,
and current signed-record cutoff obligations. No existing source theorem was upgraded
beyond its statement. No new critical estimate, Lean source/build, axiom audit, numerical
mathematical experiment, heartbeat increase, subagent, full/umbrella build or commit.
RH goal active and unmet. Next hard step remains joint signed cancellation of the complete
head and moving boundary; fixed-t truncation and the sign of the first band do not pay it.

## Active retained-boundary sign attack (2026-10-04,1005n)

Route MC. Prior turn produced no critical estimate. Its complete moving tail retains
rho times the actual source primitive; this turn attacks the sign of the retained head
and boundary together. Test the exact product expansion against the harmonic Liouville
prefix, with all cofactor bands and Abel endpoints retained. A positive continuum model
or a sign for the first band is insufficient. Corpus-based conjecture/proof analysis is
in progress; no new sign, critical bound or RH claim at this checkpoint.

### Complete boundary profile and the sign-changing recovery kernel (1005n)

**Paper analysis, not a critical estimate or Lean theorem.** Put

    h(u)=sum_(1<=n<=u)lambda(n)/n, L(u)=sum_(1<=n<=u)lambda(n),
    P(u)=u*h(u)-L(u)=integral_1^u h(v)dv, u>=1.

For c_R from1005m and C_R(X)=sum_(n<=X)c_R(n), the complete inverse identity gives,
for integer R>=1 and real u>=1,

    C_R(R*u)=1-sum_(m<=u)lambda(m)*(A(R*u/m)-A(R))
      =1-rho*R*P(u)
        -sum_(m<=u)lambda(m)*(E(R*u/m)-E(R)).                 (BP)

Indeed subtract the omitted d>R part from the full divisor sum, then sum first over its
cofactor m. If m=u is an integer, the displayed difference vanishes; no endpoint atom
is lost. The count bound makes the last sum O(u*sqrt R), uniformly for u>=1: use
sum_(m<=u)m^(-1/2)<=2*sqrt u and floor(u)<=u. Thus the complete signed boundary has
profile -rho*P(u) after division by R. The first band has P(u)=u-1 on[1,2], but all
subsequent bands keep the actual harmonic Liouville prefix. The previously inspected
harmonic theorem gives decay to zero, not a sign for h or P.

For each c>0 set W_c(u)=(1/u+c)*exp(-c*u). Full Abel summation of(BP), including the
n=1 head, yields

    lim_(R->infinity)[S_R(c/R)-(1+c/R)*exp(-c/R)]
       =rho*integral_1^infinity W_c'(u)*P(u)du
       =-rho*integral_1^infinity W_c(u)*h(u)du.

The error integral is dominated by R^(-1/2)*integral_1^infinity u*|W_c'(u)|du, finite
for this fixed c. P(1)=0 and its at-most-u*log(u) growth kill both Abel boundary terms.
The full primitive from1005m is therefore

    I(c)=integral_1^infinity h(u)*(1/u+c)*exp(-c*u)du.

This also follows directly from the complete harmonic Abel identities

    J(t)=t*integral_1^infinity h(u)*exp(-t*u)du,
    K(t)=t^2*integral_1^infinity u*h(u)*exp(-t*u)du
        =t^2*integral_1^infinity (t*u-1)*P(u)*exp(-t*u)du.    (HK)

All these fixed-positive-t interchanges and differentiations are absolute under the
elementary harmonic bound; no critical cancellation is assumed. The attempted positive
primitive comparison fails to produce an inequality for K: even if P>=0 were proved,
the last kernel changes sign at u=1/t. One must compare the two complete weighted
regions. No positivity of P is claimed, and no implication from a positive primitive
to its derivative is used. Substituting the known logarithmic cancellation in(HK)
returns logarithmic control, not the required half power. This is a diagnosis of the
attempted estimate, not a new RH receiver to formalize.

### Square-product regrouping retains a divisor-dependent lower endpoint (1005n)

The inspected exact squarefree count and reciprocal-square Mobius identity give

    E(x)=-sum_(m>=1)mu(m)*frac(x/m^2), x>=1.

The sum is absolutely convergent at each x, with unsigned bound O(sqrt x). Expanding
K'(v)=-v*sum_(n>=1)lambda(n)*n*exp(-n*v) in the original x>=1 source work is also
absolutely justified for each fixed t>0. The complete retained work becomes

    t*C(t)=t^2*sum_(m,n>=1)mu(m)*lambda(n)*n*m^2
               *integral_(1/m^2)^infinity frac(y)*exp(-t*n*m^2*y)dy. (SQ)

Grouping by k=n*m^2 does NOT remove m from this kernel. If one replaced every lower
endpoint by zero, the coefficient identity

    sum_(m^2|k)mu(m)*lambda(k/m^2)
       =lambda(k)*mu(k)^2=mu(k)

would collapse the coefficients. That replacement changes the source. The omitted
intervals correspond exactly to0<x<1, where the completed discrepancy is -rho*x.
In the source integral their contribution, whenever its limit is justified, is
-rho*(K(t)-K(0+)), hence -rho*K(t) when K(0+)=0. This is the unknown term in(SC), not
a negligible endpoint. After completing it, the original equation reduces to the
already-known completed identity -t*exp(-t).

There is an additional convergence obligation: expanding the completed integral into
the separate n-series down to x=0 has a harmonic absolute divergence. The fixed-t
x>=1 justification does not permit that expansion. No rearrangement of that completed
double series, ordinary endpoint limit, or continued harmonic sum is assumed here.
Keep(SQ)'s actual lower endpoints in any future square-product cancellation estimate.

**Assessment.** Both tests retained the actual coefficients and identified why the
proposed sign/cancellation step is unpaid. Neither bounds the full signed work or moves
the critical exponent. No route is retired. Next conjecture must estimate the retained
divisor-dependent boundary in(SQ) together with its head; grouping coefficients after
erasing that boundary, or proving another transform identity, is not progress on MC.

### 1005n source and execution ledger

Three documented deep searches reached terminal exit0:
`Liouville squarefree inverse signed sampling negative record renewal Mellin cancellation`;
`Liouville harmonic partial sums positivity Turan negative counterexample`;
`squarefree counting discrepancy integral primitive cancellation Liouville`.
partial=false/true/false; files65202/65203/65227; compiled43/stale2660 each;
compiler-pending49167/49168/49192. Snapshot/current generations1223009/1223010,
1223025/1223055,1223059/1223064. All report older-generation and unavailable semantic
coverage, background refresh, no pending method invalidation. Second reports a semantic
retrieval deadline. Available candidate/source statements and ingredient chains inspected;
proof_ideas empty. No whole-corpus absence claim.

The first generated chain supplies pointwise products, not the missing signed estimate.
The second incorrectly uses liouvilleRate_pos, whose source is exp(-N^2), to propose
arithmetic harmonic positivity; its log-decay inputs contain no sign. The third combines
squarefree density positivity with a different block-deletion square identity, without
a bridge to C(t). All are rejected. Read actual harmonic square-dilation/Abel source,
squarefree count identities, reciprocal-square density, and the dyadic Gram theorem;
the latter still concerns an additive quadratic channel, not K.

No Lean source edit/build/axiom audit, numerical mathematical experiment, added axiom,
placeholder, heartbeat increase, subagent, full/umbrella build, commit or no-go retirement.
All new displayed deductions remain PAPER. RH goal active and unmet.

## Active coupled quadratic attack (2026-10-04,1005o)

Route MC. Previous turn made no critical-bound progress. The complete product kernel
for J_lambda is not PSD on arbitrary coefficient vectors, but the actual Mobius source
has a vanishing harmonic sum. Test whether retaining that exact cancellation permits
a constrained quadratic lower bound, including every moving-cutoff boundary term.
Neither constrained positivity nor a source norm bound is assumed. Corpus search and
source-specific proof analysis in progress; no new RH or critical estimate claim.

### Harmonic centering does not supply the quadratic sign (1005o; PAPER)

Use C12.91's literal square-divisor count a=one*squareIndicator and positive kernel

    A(t)=sum_(r>=1)a(r)*exp(-r*t)/r.

The original source is J(t)=sum_(m,n>=1)mu(m)*mu(n)*A(t*m*n)/(m*n), absolutely for t>0.
The failed arbitrary-vector PSD test cannot be repaired by imposing only zero harmonic
mass. Fix positive integers u<v. Since A(z)/exp(-z)->1 at infinity, for sufficiently
large tau the two-index matrix A(tau*i*j), i,j in{u,v}, has negative determinant.
Choose real weights x,y with negative quadratic value. Add a third index L with weight
z=-x-y. The new weights have zero sum, while all new matrix terms tend to zero as L
tends to infinity. Thus the negative value persists. For the original 1/(m*n) convention,
the coefficients are u*x,v*y,L*z and their harmonic sum is zero. A common rescaling can
also make all coefficient magnitudes at most one. These are not actual Mobius coefficients.
This excludes only the proposed generic implication from harmonic centering to PSD.
No no-go is retired or asserted as a statement about J.

For the actual cutoff H_R=sum_(n<=R)mu(n)/n, anchoring at a fixed positive index v gives
the exact identity

    Q_R(t)=sum_(m,n<=R)mu(m)*mu(n)/(m*n)
       *[A(t*m*n)-A(t*v*m)-A(t*v*n)+A(t*v^2)]
       +2*H_R*sum_(m<=R)mu(m)*A(t*v*m)/m-H_R^2*A(t*v^2).

For fixed t>0, H_R->0 and the other sum converges absolutely, so the last two terms
vanish. A moving cutoff still requires their joint estimate; the limit does not assert
a sign for the anchored kernel. No generic kernel theorem from the search supplies it.

### Exact arithmetic completion of the comparable and noncomparable sectors

The additive anti-diagonal in `MobiusDivisorMonotoneSignLaw` is essential. Its sign law
cannot be substituted for a bound with the product kernel A(t*m*n). Instead retain the
actual complete coefficient at each product. For q>=1 define the finite sums

    b(q)=sum_(r*m*n=q, m|n) a(r)*mu(m)*mu(n),
    d(q)=sum_(r*m^2=q) a(r)*mu(m)^2,
    c(q)=sum_(r*m*n=q, m does not divide n, n does not divide m)
             a(r)*mu(m)*mu(n).

The two comparable orientations intersect precisely on the diagonal, hence

    lambda(q)=2*b(q)-d(q)+c(q).                              (SECT)

Here b and d are multiplicative: in the comparable orientation the only nonzero
local pairs of exponents of(m,n) are(0,0),(0,1),(1,1). At a prime, with formal variable X,
the local coefficient series of a is1/((1-X)*(1-X^2)); therefore those of b and d are

    b: (1-X+X^2)/((1-X)*(1-X^2))=(1+X^3)/(1-X^2)^2,
    d: (1+X^2)/((1-X)*(1-X^2)).

These are coefficient identities of formal series, not analytic Euler limits. Explicitly,

    d(p^(2k))=d(p^(2k+1))=2k+1,
    b(p^(2k))=k+1, b(p^(2k+1))=k.

Thus b(q)>=0 and d(q)>=1. The full noncomparable coefficient is also nonnegative.
To prove it, write q=product_i p_i^e_i with e_i>0, put

    D_i=2*floor(e_i/2)+1, s_i=(-1)^e_i,
    B_i=(D_i+s_i)/2, C_i=(D_i-s_i)/2.

All B_i>=0 and C_i>0. From(SECT),

    c(q)=product_i D_i+product_i s_i-2*product_i B_i
        =2*sum_(S subset indices, |S| even, S nonempty)
                product_(i in S)C_i * product_(i notin S)B_i >=0. (EVEN)

Expansion of product(B_i+C_i)+product(B_i-C_i) proves the second equality, retaining
every subset. It also gives the exact zero class: c(q)=0 precisely when q=1, q is a
positive prime power, or q is squarefree with an odd number of prime factors. For a
number with at least two prime factors and some exponent>=2, choose a nonempty even
subset containing all exponent-one primes; such a subset exists, and its term is
strictly positive. For squarefree q, only the full subset survives, giving c(q)=2 for
positive even factor count and zero for odd factor count.

These statements concern the complete a-convolved product coefficients. They assert
neither positivity of an arbitrary quadratic form nor a sign for each uncompleted
noncomparable Mobius pair. Full fixed-t absolute convergence permits the identities

    B(t)=sum_q b(q)*exp(-q*t)/q >=0,
    D(t)=sum_q d(q)*exp(-q*t)/q >=0,
    N(t)=sum_q c(q)*exp(-q*t)/q >=0,
    J(t)=2*B(t)-D(t)+N(t).                                  (BAL)

This is a paper source-order law. Its arithmetic and analytic formalization is OPEN;
it is not reported as a Lean result or as critical cancellation.

### The remaining comparison has an explicit critical-scale allowance

The b Euler coefficient identity gives the positive full expansion

    B(t)=sum_(r,s>=1; d>=1 squarefree)
              exp(-t*r^2*s^2*d^3)/(r^2*s^2*d^3).

Its value B(0) is finite. For every0<alpha<1/2, the elementary inequality
1-exp(-u)<=u^alpha for u>=0 and Tonelli give

    0<=B(0)-B(t)
       <=t^alpha*(sum_r r^(-2+2alpha))^2
                  *(sum_(d squarefree)d^(-3+3alpha)).        (ALLOW)

Every series displayed on the right converges in its ordinary absolute chamber.
This pays the critical allowance without a bound on the signed source or a contour shift.
In contrast D(t) diverges as t decreases to zero: its m=1 diagonal contains A(t), and
a(r)>=1 gives A(t)>=sum_r exp(-r*t)/r, which diverges. The harmonic Abel limit J(t)->0
then forces N(t)=D(t)-2*B(t)+o(1). Separate positivity of B,D,N therefore leaves a large
compensation between D and N; it does not provide a quantitative error for that balance.

**Next concrete conjecture, still OPEN:** the actual full functions satisfy

    D(t)-N(t)<=2*B(0), t>0.                                 (CEILING)

If proved, (BAL)/(ALLOW) would yield J(t)>=-2*(B(0)-B(t))>=-C_alpha*t^alpha for every
alpha<1/2, paying the original one-sided MC target. This is a candidate stronger
comparison, not an assumed premise or a new receiver theorem. The exact centered gap is

    2*B(0)-D(t)+N(t)=2*(B(0)-B(t))+J(t).

The coefficient2*b(q)-lambda(q) is not nonnegative: at a squarefree product of two
distinct primes, b(q)=0 and lambda(q)=1. Thus a completely monotone positive-coefficient
argument does not establish(CEILING). The positive even-subset formula(EVEN) also does
not compare N to D at this scale. The hard next work is this full arithmetic comparison,
with all squarefree parity channels retained, not a refinement of(ALLOW)'s constants.

**Assessment.** New paper positivity and exact zero-class structure for the completed
noncomparable coefficients emerged from the actual-source test. No bound on the crucial
D/N compensation was proved. The original RH-critical estimate is still open. No generic
PSD assumption, unchanged old receiver, numerical experiment, or toy-kernel counterexample
has been presented as progress on that estimate. No no-go or route retired.

### 1005o corpus/execution ledger

Four documented deep searches reached terminal exit0, queries:
`Liouville Mobius quadratic square cofactor kernel signed boundary lower bound`;
`Mobius product kernel harmonic zero mass constrained quadratic Liouville positivity`;
`Mobius comparable pairs squarefree coprime product quadratic Liouville`;
`Mobius noncomparable square divisor Liouville coefficient nonnegative completion`.
partial=true/false/true/false. Snapshots65235/65237/65237/65240 files;
compiled43/stale2660 each; compiler-pending49197/49199/49199/49201.
Snapshot/current generations1223190/1223191,1223199/1223200,1223208/1223218,
1223282/1223287. All older-generation/semantic-coverage warnings, background refresh,
no method invalidation pending. First reports interrupted text retrieval; third reports
semantic deadline. Candidate/source statements and proposed ingredient chains inspected;
proof_ideas empty. No whole-corpus novelty/absence claim follows from these snapshots.

Energy-to-RH chains retain the unknown energy hypothesis. PositiveKernelData contains
quadratic positivity as a field; Christoffel positivity assumes a positive moment form.
Neither gives a sign for A(t*m*n). Coprime-product and CRT identities do not prove the
new sector inequality. The final chain's square-indicator identity and signed prime
quotient identity do not by themselves imply nonnegative completion; the explicit local
coefficient and even-subset proof above is required. Read the actual short quadratic
reconstruction, harmonic/Dirichlet Liouville identities, additive comparable sign law,
primitive-ratio localization and multiplicative rectangle source. The rectangle estimate
still requires an arithmetic covering and control of the entire uncovered residual.

No Lean source edit/build/axiom audit, added axiom, placeholder, heartbeat increase,
numerical mathematical experiment, subagent, full/umbrella build or commit. New results
and(CEILING) analysis remain PAPER, with formal status OPEN. Goal active and unmet.

## Active centered-ceiling attack (2026-10-04,1005p)

Route MC. Revalidated1005o's sector definitions and local coefficient proof. That turn
identified paper source order but did not bound the critical compensation. This turn
attacks 2*B(0)-D(t)+N(t)>=0 for the actual coefficients. Test divisor-square positivity
and the exact multiplicative structure against the full centered kernel; retain all
gcd/lcm changes, cutoff terms and source moments. No PSD, sign or RH premise is assumed.

### 1005p: complete lcm correction, with its parity retained (PAPER)

No critical cancellation estimate was obtained. The divisor-square theorem inspected
in `Sieve/HarmonicWeightedGrahamMeanSquare` concerns a kernel of lcm(m,n), whereas
the full MC quadratic source has a kernel of m*n. The following calculation tests
the exact difference; it does not transfer positive definiteness between them.

Keep a=one*squareIndicator and A from1005o, and put f_t(u)=A(t*u)/u. For fixed t>0,

    J(t)=sum_(m,n>=1) mu(m)*mu(n)*f_t(m*n),
    L(t)=sum_(m,n>=1) mu(m)*mu(n)*f_t(lcm(m,n)).

Both sums converge absolutely. For the second, grouping by lcm label k gives at
most k^2 pairs; f_t(k) decays exponentially. Expanding the square-divisor count gives

    f_t(l)=sum_(s>=1) s^-2 * sum_(k>=1, l|k) exp(-t*s^2*k)/k.

Thus the complete lcm quadratic form is a positive divisor square, and Mobius
inversion collapses it exactly:

    L(t)=sum_s s^-2 * sum_k exp(-t*s^2*k)/k * (sum_(d|k)mu(d))^2
        =sum_s exp(-t*s^2)/s^2.

This is the already-known positive square forcing, not a new bound on J.

For a squarefree lcm label k, write g=gcd(m,n). Then m=g*u, n=g*v,
g*u*v=k, and the three factors are pairwise coprime. The full product and lcm
contributions at this label are respectively

    J_k(t)=sum_(g|k) mu(k/g)*2^omega(k/g)*f_t(g*k),
    L_k(t)=mu(k)*f_t(k).

With T_p f(u)=f(p*u) and P=primeFactors(k), this says

    J_k(t)=mu(k) * [product_(p in P)(2*Id-T_p) f_t](k).

The operator product has an actual nonnegative coefficient expansion. Its coefficient
at n replaces a(p^e) by 2*a(p^e)-a(p^(e-1)) for each p in P and e>=1; at e=0 its
local coefficient is2. All other local factors remain a(p^e). Call the resulting
coefficient a_P(n). Since a(p^e)=floor(e/2)+1 is nondecreasing, a_P(n)>=a(n), and
a_P(1)=2^card(P). Therefore, for every squarefree k>1,

    J_k(t)-L_k(t)=mu(k)*H_k(t),
    H_k(t)=sum_(n>=1)(a_P(n)-a(n))*exp(-t*k*n)/(k*n)>0.

This gives the exact sign of each completed correction fibre. It does not sign their
sum: odd and even squarefree labels have opposite signs. In particular, for every
prime p,

    H_p(t)=f_t(p)-f_t(p^2)>=(1-1/p)*f_t(p) -> infinity as t decreases to0.

Here A(t*p^2)<=A(t*p), and A(t*p)>=sum_n exp(-t*p*n)/n tends to infinity.
Consequently even one negative correction fibre cannot be paid by a constant times
B(0)-B(t), which tends to0. Complete inter-fibre cancellation is indispensable.
This is a paper diagnosis of the attempted termwise comparison, not a falsification
of CEILING, a Lean no-go certificate, or a retired route.

### Direct cumulative and prime-insertion tests (PAPER / open sign)

The positive sector b is supported exactly on1 and the powerful integers: every
positive prime exponent must be at least2. Define, for x>=0,

    h(x)=sum_(1<=n<=x)lambda(n)/n,
    T_b(x)=sum_(n>x)b(n)/n,
    G(x)=h(x)+2*T_b(x).

Absolute exponential interchange and B(0)<infinity give the exact identity

    2*(B(0)-B(t))+J(t)=t*integral_0^infinity exp(-t*x)*G(x) dx.

The stronger direct comparison G(x)>=0 would therefore prove CEILING. Also
T_b(x)<=x^-alpha*sum_n b(n)/n^(1-alpha) for every0<alpha<1/2 and x>0,
with a finite moment. The difficult statement is the sign of G, not this positive
tail estimate. Existing logarithmic harmonic decay does not imply that sign or the
needed power bound. No order-preserving inversion theorem was found applicable to
this signed prefix. The inspected monotone Mobius theorem has weight n^-2 and an
increasing function of u/n; its hypotheses do not hold for the asserted comparison.

A finite-prime induction retains a useful explicit forcing, but has not closed.
For finite P define J_P, B_P by restricting their coefficients to P-smooth integers,
delta_B_P(t)=B_P(0)-B_P(t), and F_P=J_P+2*delta_B_P. For p outside P let
R_p f(t)=sum_(e>=0)(-1)^e*p^-e*f(p^e*t). The local coefficient identities give

    b_p(X)-(1+X)^-1 = X/((1-X)*(1-X^2)),

and hence the exact full insertion law

    F_(P union {p})(t)=R_p F_P(t)
      +2*sum_(e>=1) floor((e+1)/2)*p^-e*delta_B_P(p^e*t).

All series converge absolutely: the functions are bounded and the displayed
coefficients have geometric decay. The forcing is nonnegative. Nevertheless R_p
does not preserve arbitrary nonnegative functions; pairing its consecutive powers
still requires control of F_P(u)-F_P(p*u)/p. This control has not been proved for
the actual F_P. Positivity of the forcing alone does not close induction. Requiring
another derivative cone without proving this arithmetic comparison would repeat the
earlier unclosed hierarchy. Neither G>=0 nor this insertion comparison is assumed.

**Assessment and next hard work:** these tests expose the precise parity correction
and a positive insertion forcing but do not move the RH-critical estimate. No new
formal receiver or easy coefficient lemma was added as a substitute. Continue with
the actual coupled comparison G, or prove a signed bound for the complete insertion
sum; do not repeat the lcm PSD transfer or pay individual negative fibres from B.
The full J lower bound, CEILING, K sign and RH remain OPEN.

### 1005p corpus/execution ledger

Five documented deep searches reached terminal exit0: divisor-square centered energy;
lcm/product correction; full Liouville parity sign; damped/half parity; cumulative
harmonic/powerful tail. In that order partial=false/true/false/false/false; files
65253/65254/65256/65256/65256; compiled43 and stale2660 throughout; compiler-pending
49209/49210/49212/49212/49212. Snapshot/current generations1223442/1223443,
1223480/1223480,1223490/1223494,1223494/1223497,1223519/1223519.
All reported semantic coverage unavailable and background refresh; searches1,3,4
also reported older-generation snapshots. No pending method invalidation.

All returned candidate statements, source arguments, proof ideas and ingredient sets
were inspected. Floor inversion, squarefree density and positive divisor-square tails
do not supply the missing sign. Energy-to-RH consumers retain their energy premises.
The generated chains applying the complex harmonic-function Liouville theorem to
arithmetic Liouville partial sums are inapplicable. The Beukers lcm arithmetic kernel
has a different definition; no transfer was made. `DampedMobiusSumsZeroFree` supplies
an exact nonnegative divisor sum, not a sign for its incomplete harmonic inverse.
`PrimeSieveHarmonicInclusionExclusion` retains its decimated harmonic weights; it is
not a bare truncated Mobius positivity theorem. One unmatched shell glob was corrected
by a file inventory; no source file was affected.

No Lean source changed, no Lean build or axiom audit was run, and no new Lean theorem
is claimed. No numerical mathematical experiment, axiom, placeholder, heartbeat raise,
subagent, full/umbrella build, commit or no-go retirement. Goal remains active/unmet.

## Active coupled-prefix attack (2026-10-04,1005q)

Route MC. Previous turn gave paper diagnostics, no critical estimate. Current hard
target is the actual inequality h(x)+2*T_b(x)>=0, or a weaker all-subcritical-power
lower bound for h sufficient for J. Revalidated the preceding definitions and the
literal signed-cofactor source. Test prime deletion with the complete prefix and
powerful tail retained; do not infer a sign from an inversion identity or ignore
the nondivisible cofactor remainder. No new sign premise is assumed.

### 1005q actual Euler-baseline test (PAPER; not a retired no-go)

The stronger proposed induction estimate

    h_P(x)>=ell_P-C*T_(b,P)(x),
    ell_P=product_(p in P)(1+1/p)^-1,

cannot hold uniformly over finite prime sets for any fixed C. Here h_P and the b-tail
retain every P-smooth prime power, and ell_P is the full harmonic Liouville sum on
that finite monoid. This failure does not refute G>=0 or the density ceiling.

Take P_R to be all primes in(R,2R] and x_R=R^(3/2). Put
S_R=sum_(p in P_R)1/p and Q_R=sum_(p in P_R)1/p^2. The inspected corpus PNT implies
S_R is bounded above and below by positive constants times1/log R. Thus S_R->0,
R*S_R->infinity, and Q_R<=S_R/R=o(S_R^2). For all sufficiently large R, every selected
prime is below x_R and every product of two selected primes, including repetitions,
is above x_R. The literal prefix is consequently

    h_(P_R)(x_R)=1-S_R.

The b-prefix contains only n=1, because every nontrivial supported integer is
powerful and is at least R^2. Its full tail is B_(P_R)(0)-1. Uniform Taylor estimates
on0<=1/p<=1/R, with the complete Euler products retained, give

    ell_(P_R)=1-S_R+(S_R^2+Q_R)/2+O(S_R^3+S_R*Q_R+Q_R/R),
    B_(P_R)(0)-1=2*Q_R+O(Q_R/R+Q_R^2).

For the second line use b_p(z)=(1+z^3)/(1-z^2)^2; its logarithm is2*z^2+O(z^3).
For the first use log ell=-S_R+Q_R/2+O(Q_R/R), then exponentiate. Therefore

    [ell_(P_R)-h_(P_R)(x_R)-C*T_(b,P_R)(x_R)]/S_R^2 -> 1/2.

The retained distinct-prime contribution has second-order mass S_R^2, which the
powerful tail Q_R cannot pay. Meanwhile G_(P_R)(x_R)=1-S_R+O(Q_R)->1, so the tested
family stays positive. A comparison to its Euler baseline was stronger than the
required sign and is the step rejected. This is an analytic paper family, not a
numerical experiment, critical cancellation bound or audited Lean obstruction.

### Nonnegative counting error still leaves signed record work (PAPER)

The full divisor identity lambda*one=squareIndicator gives

    sum_(m>=1)K(m*t)/m = sum_(s>=1)(1+t*s^2)*exp(-t*s^2)/s^2.

Repeat the complete Abel calculation with floor(x)=x-frac(x). The result, with every
endpoint retained, is

    K(t)=Q(t)-t*integral_1^infinity frac(x)*K'(t*x)/x dx,
    Q(t)=t*sum_(s>=1)exp(-t*s^2)>0.

For fixed t>0 the coefficient expansions and integrals are absolute. Unlike the
squarefree discrepancy, frac(x) is nonnegative; that does not determine the sign of
its pairing with K'. At a negative record of u^-a*K(u),0<a<1/2, define
R_t(u)=K(u)-K(t)*(u/t)^a>=0 for u>=t. Then

    (1+a*I_a)*K(t)=Q(t)-D_t,
    I_a=integral_1^infinity frac(x)*x^(a-2)dx,
    D_t=t*integral_1^infinity frac(x)*R_t'(t*x)/x dx.

I_a is finite and nonnegative. R_t(t)=0, but its derivative is not signed. For integer
cutoffs N, integration by parts across every floor jump gives exactly

    D_t=lim_(N->infinity)[sum_(2<=n<=N)R_t(t*n)/n
               -integral_1^N floor(x)*R_t(t*x)/x^2 dx].

The boundary frac(N)*R_t(t*N)/N is zero. For noninteger cutoffs it tends to zero
because R_t(t*x)=O(x^a) at infinity. The two nonnegative pieces in this compensated
limit generally diverge; they must not be separated. The record condition alone
does not compare the sampled values with their integral. No upper bound D_t<=Q(t),
or critical allowance for their difference, was proved. Changing the counting error
to a nonnegative one has therefore not established a maximum principle for K.

### Return to the primitive without requiring the stronger K sign

P(x)=x*h(x)-sum_(n<=x)lambda(n)=sum_(n<=x)lambda(n)*(x/n-1) is the primitive from1005n.
Its sign has not been established. That section correctly noted that P>=0 would not
sign the K kernel. For the actual final density J, however, the direct identity is

    J(t)=t^2*integral_1^infinity P(x)*exp(-t*x)dx.

Thus P>=0 would suffice directly, and even P(x)>=-C_epsilon*x^(1/2+epsilon) for
every0<epsilon<1/2 would give the required J lower bound. This follows by absolute
integration by parts at fixed t, since P has at most x*log(x) growth. It is a guide
to the source inequality to prove, not an added conditional Lean receiver.

Tested the complete finite quadratic expression. For any arithmetic f let
W_f(y)=sum_(n<=y)f(n)*(y/n-1), zero for y<1. With a=one*squareIndicator and
U=floor(sqrt x), finite hyperbola splitting of lambda=mu*mu*a yields

    P(x)=2*sum_(m<=U)mu(m)*W_squareIndicator(x/m)
          -sum_(m,n<=U)mu(m)*mu(n)*W_a(x/(m*n)).

Every omitted pair would have m,n>U and hence m*n>x; the two sums retain all other
terms. This does not give a positive quadratic form. At x=U^2, U>=2, its matrix
has W_a(x/U^2)=W_a(1)=0 and W_a(x/U)>0, so its two-point minor on1,U is negative.
The actual Mobius vector is fixed; generic PSD cannot replace its signed comparison.
No sign or half-power lower estimate for this complete triangular source was obtained.

**Assessment:** no RH-critical frontier movement or new Lean theorem. The actual
prime-interval family changes the admissible induction step: the full Euler-baseline
error cannot be bounded by the powerful tail alone. The fractional record and finite
hyperbola tests retain the unresolved signed work. Continue by proving a lower bound
for the literal triangular P source, without requiring a derivative sign or replacing
the full arithmetic vector with a generic PSD claim. G, CEILING, K and RH remain open.

### 1005q corpus/execution ledger

Four documented deep searches all terminal0 and partial=false: prefix/deletion;
fractional-part renewal; integrated Riesz sign; triangular/hyperbola source. Files
65260/65261/65264/65266; compiled43 and stale2660 throughout; compiler-pending
49215/49215/49217/49219. Snapshot/current generations1223566/1223566,
1223588/1223592,1223620/1223620,1223638/1223638. All reported semantic coverage
unavailable and background refresh; second also older-generation warning. No pending
method invalidation. Candidates, source arguments, proof ideas and ingredient sets
inspected; generated harmonic-function, vortex, nonnegative weight and energy-consumer
chains do not prove the arithmetic sign. The two Liouville sieve sources retain
sigma>=1 or sigma>1, complete Perron errors and unsigned mean-square bounds; their
statements do not control the triangular source at the needed power. Prime availability
in the paper family uses `Sieve/PrimeCountingBigO.primeCounting_sub_logIntegral_isBigO`.
Two incorrectly located sieve paths were corrected by file inventory before reading.

No Lean source/build/audit, numerical mathematical experiment, axiom, placeholder,
heartbeat raise, subagent, full/umbrella build, commit or no-go retirement. Paper
diagnostics remain unaudited in Lean. Goal active/unmet; cleanup in working log.

## Active triangular-quadratic attack (2026-10-04,1005r)

Route MC. Revalidated1005q's exact short expression for P. Prior turn changed one
admissible comparison through a paper prime-interval test, but supplied no critical
bound. This turn targets the combined lower bound, retaining both short Mobius sums
and all divisor constraints. No generic PSD, Euler-baseline bound or derivative sign
is imported. Current corpus search and source inspection precede any Lean addition.

### Actual short-head obstruction under verification (1005r)

Write `H(U)=sum_{m<=U} mu(m)/m`, `V(U)=sum_{m<=U} mu(m)/sqrt(m)`,
and `A(U)=sum_{m<=U} mu(m) W_square(U^2/m)`. The proposed positive survivor is
`A(U)-zeta(2) U^2 H(U)=o(U^(3/2))`; the obstruction is
`A(U) != o(U^(3/2))`. Both concern the actual coefficients, not an arbitrary
vector in the product kernel.

Paper argument: if `r=sqrt(y)` and `q=floor(r)>=1`, reciprocal-square integral
comparison gives `1/(q+1)<=sum_{s>q}1/s^2<=1/q`. Consequently
`|W_square(y)-zeta(2)y+2sqrt(y)|<=1`: the upper residual is at most
`(r-q)^2/q<=1`, and the lower residual is at least
`(r-(q+1))^2/(q+1)-1>=-1`. Summing with the literal Mobius coefficients gives
`A(U)=zeta(2)U^2 H(U)-2U V(U)+O(U)`. The corpus PNT `M(U)=o(U)` and Abel
summation imply `V(U)=o(sqrt(U))`. If `A(U)=o(U^(3/2))`, then
`H(U)=o(U^(-1/2))`. But the exact inverse Abel law
`M(U)=(U+1)H(U)-sum_{m<=U}H(m)` would give `M(U)=o(sqrt(U))`, contradicting
the corpus's unconditional `MertensSquareRootOmega` theorem.

This would rule out estimating the two short terms separately by absolute
values at every half-plus-epsilon exponent. It does not bound their combined
value or refute a one-sided short-head bound. Lean status: OPEN. No route is
retired by this checkpoint.

### Formal closure of separate short-head payment (1005r)

The proposed positive survivor and obstruction above are now unconditionally
formalized in `LiouvilleTriangularShortHead.lean`. In namespace
`RHTower.LiouvilleTriangularShortHead`, `mobiusShortHead_asymptotic` proves the
actual asymptotic, `not_harmonic_isLittleO_inv_sqrt` supplies the weighted Mobius
obstruction, and `not_mobiusShortHead_isLittleO` excludes separate sub-three-quarter
absolute payment in x. `squareTriangle_remainder` proves the complete square-tail
remainder. These statements do not assert two-sided signed excursions or exclude
a one-sided short-head bound. The reconstruction of the full P remains paper-level
here; no new critical lower estimate is claimed.

Positive survivor and dependency-closed proof:
`../3-formalized/mc-triangular-short-head-scale-law.md`.
Only the separate-absolute-payment construction is retired:
`../5-failed/mc-triangular-short-head-absolute-payment.md`.

Targeted `lake --old build GaloisForLFunctions.RHTower.LiouvilleTriangularShortHead`
passed, reporting the leaf built in135s. Required direct
`lake --old env lean GaloisForLFunctions/RHTower/LiouvilleTriangularShortHead.lean`
passed without diagnostics. Four public axiom checks from `/tmp` all report only
propext/Classical.choice/Quot.sound. Umbrella wired once; no umbrella build. Index
regeneration passed. Global lint reports13 unrelated unreachable modules, none
for this leaf. Four deep corpus searches all exited0 with partial=false; their
coverage and source freshness are recorded in the survivor card. No numerical
mathematical experiment, added axiom, placeholder, heartbeat raise, subagent,
full build, commit or push.

**Assessment:** new actual-source obstruction and positive asymptotic proved;
no advance in the critical exponent of the full signed lower bound. Next attack
must control the coupled two-term expression, retaining the moving harmonic
prefix contribution inside its cancellation. Bounding that contribution in
isolation is excluded; another conditional receiver would not solve the problem.

## Active joint quadratic attack (2026-10-04,1005s)

Route MC. Previous turn was progress: the actual short-head obstruction and its
positive asymptotic were formalized and audited. The critical lower bound for the
complete P=2A-B did not improve. Revalidated the current leaf and active ledger.
This turn targets the interaction between both terms, retaining exact Mobius
divisor constraints and the full square kernel. No separate absolute payment of A,
no generic PSD substitution, and no unproved sign of a derivative will be used.
Current corpus search precedes the next source-level conjecture.


## Shifted-pole cancellation (2026-10-04,1005s)

**Route MC; hard target unchanged:** P(x)>=-C_epsilon*x^(1/2+epsilon). The joint positivity, rough-prime recursion, negative-record renewal and pole-subtracted quadratic attempts did not establish that estimate. In particular, the retrieved Buchstab identity is exact bookkeeping, while the Dickman/Wick characteristic function is a different positive source. Neither supplies the missing signed comparison. No generic PSD substitution or derivative sign was assumed.

A concrete new argument then emerged from the actual moving head. Its exact square-kernel remainder gives, on paper, |E(x)|<=sqrt(x) and

```
M_A(s)=Z/((s-1)*zeta(2s-1))
       -2/((s-1/2)*zeta(2s-1/2))+M_E(s).
```

The new audited Lean leaf `LiouvilleTriangularPoleSeparation` proves the needed analytic separation: some w has 3/4<=Re(w)<1, nonzero imaginary part, zeta(2w-1)=0, but zeta(w) and zeta(2w-1/2) are nonzero. At one such w the complete three-term pole model is analytic iff its short-head coefficient vanishes. The proof starts from the corpus's Hardy zero and rules out endless zero propagation under rho->(rho+1)/2 by the nonzero residue unit at1. No zero was computed.

This is new rigorous progress on pole cancellation, not a critical lower bound. The proposed source consequence is two-sided supercritical excursions of P+c*A for every c!=0, including -B=P-2A. Its exact Mellin identities, remainder regularity and Landau step still require Lean proofs. The separate one-sided payment construction is NOT retired. Parent: `mc-triangular-quadratic-pole-cancellation.md`; audited component: `../3-formalized/mc-triangular-shifted-pole-separation.md`.

**Validation:** targeted `lake --old build` leaf exit0 (146s,10064 dependency jobs); required direct `lake --old env lean` leaf exit0 without diagnostics. Two `/tmp` public axiom audits exit0, only propext/Classical.choice/Quot.sound. An initial extra API-check driver had universe-inference errors; those were fixed in the driver. Unique umbrella import and three generated API entries checked. Index regeneration exit0. Global lint exit1 with16 unrelated unreachable modules, no new-leaf error. No heartbeat increase, computation, added axiom, placeholder, subagent, full/umbrella build, commit or push.

**Six documented searches**, all terminal exit0; candidates, source arguments, ideas and ingredient sets inspected. Joint-quadratic/parity-pairing/rough-prime-flow/renormalized-quadratic/pole-cascade/weighted-Mellin had partial flags false/true/true/false/false/false. File counts65291/65290/65308/65311/65311/65322; pending49231/49231/49244/49246/49246/49255; compiled43 and stale2660 throughout. Snapshot/current generations1224057/1224059,1224049/1224057,1224143/1224144,1224180/1224180,1224224/1224230,1224337/1224338. All reported background refresh and unmeasured semantic coverage; all except renormalized-quadratic reported older-generation warnings. The rough-prime query reported a semantic request timeout and used its available partial results. Generated chains through unrelated Gibbs/triangular positivity were rejected as source mismatches.

**Next obligation:** connect this proved pole rigidity to the actual source via the two Mellin formulas and Landau, retaining E and the moving lower endpoint m^2. The inspected `StepProfileMellinLSeries`, mathlib `LSeries_eq_mul_integral` and `mellin_differentiableAt_of_isBigO_rpow` provide relevant APIs, not already-checked source proofs. Do not relabel the normal-form result as a theorem about the physical quadratic sum or RH.
