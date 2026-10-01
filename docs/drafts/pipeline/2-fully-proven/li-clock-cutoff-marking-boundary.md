# Actual cutoff positivity boundary and exact marking inverse

- **ID:** LI-CLOCK-CUTOFF-MARKING-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / exact same-source boundary and positive survivor
- **Parent:** [integrated source sign](../1-in-progress/li-clock-integrated-source-sign.md)
- **Earlier survivor:** [Gamma cumulative reserve and marking](li-clock-gamma-cumulative-reserve-marking.md)
- **Statement:** Full actual cutoff D_a(T)=integral_0^T exp(-at)P(t)/t is strictly positive for every a>=beta,T>0, where beta is the maximal absolute imaginary reciprocal frequency. If beta>0, every real a<beta has a common-phase cofinal negative escape. Beta0 is RH and gives every real damping. For p>1/sqrt150 the actual exponentially marked signed Gamma intensity has an exact positivity range and positive leading mode with full factorial signed-error bounds.

## Gates and limits

- [x] Complete609-line author paper I1–I25 and all source/sum/integral admissions.
- [x] Root ALL609 audit and relevant primary-source checks.
- [x] Independent Pole ALL609/I1–I25 audit, read in full by root.
- [x] Scalar I8 cosh–cos finite cutoff positivity: [exact Lean survivor](../3-formalized/li-clock-cosh-cos-cutoff.md), two public declarations and complete final gates.
- [ ] Exact new cutoff, marking-boundary and all-order survivor formalized in Lean.

The inverse kills the positive leading mode exactly. Positivity of the marked density does not orient its derivative remainder. Original P>=0, the undamped D0 source proof and RH remain OPEN. Scalar I8 is formalized; full actual-source classification remains Lean-open. No route retirement, actual negative witness or unconditional not-RH conclusion. Gamma-row/CP constructions retain p>1/sqrt150; finite-cutoff statements have their separately proved real damping domains.

## Immutable complete proof and audit

Author `/tmp/li_producer_theta_marking_inverse_attack.md`,609 lines,SHA256
`f0a69b3cd1729e7ad9a8eb3620904c5b91078b122e1e5d72d178a9bdff6b30fa`.
Root `/tmp/li_root_theta_marking_inverse_review.md`,complete review PASS.
Independent `/tmp/li_pole_theta_marking_inverse_audit.md`,104 lines,SHA256
`3f31beec745d146d082a1c9a45680a52e1d20298e89858743bb5929d8d114c9b`,PASS.
All61 deep and9 displayed lexical dispositions retained; coverage is qualified,
with no corpus-absence or world-novelty claim. Frozen paper follows verbatim.

# Actual theta marking: inversion attack and retained signed information

Scope: PAPER ONLY. Literal actual single-Xi primitive P and complete Gamma
rows; no Lean/compiler/numerics/tree edits. Parent's unsmoothed N17 target
P(t)>=0 for all t>0 remains OPEN. This note develops a new source-level
attempt; every new conclusion requires independent paper audit.

Chosen mechanism, recorded before derivation: sharpen the complete reserve,
then use the exact marked density's positive leading exponential and signed
remainder to test positivity-preserving removal of the mark. Also inspect
endpoint marking limits and finite compositions. Marking is injective: the
issue is preservation of its positive cone under the differential inverse,
not loss of exact mathematical information.

Corpus-first direct query completed before these claims:

    python3 scripts/formal_tools.py research 'actual theta exponential marking Gamma intensity positive inverse resolvent compound Poisson primitive cumulative reserve' --mode deep --budget-seconds 150 --no-refresh --json

Owned session36552 terminal0, elapsed53.243085375s; partialfalse,
errors0/unfinished0. All61 retained records have now been read:20candidate
contracts,20source arguments including every returned proof/method excerpt,
10prose passages,10Lean passages,1ingredient set. No other hit arrays.
Index1168673; inventory63689allindexed; coverage1168674/current1168679.
Lean53425/prose10264; declarations827316/docs2390690/vectors2239411.
Compiler43snapshot,2error,48027pending,2660stale,38stalesnapshot,
1umbrellasourceonly,2654unavailable,10264notapplicable. Methods397673ready,
186219stale,43failed. Semanticunmeasured/reportingbudget; oldercoverage
warning. Source-only retrieval is not a new compiler or applicability gate.
Complete retained JSON remains in session tool store marking_inverse_results;
all-hit dispositions and relevant exact primary anchors follow below.

Baseline: /tmp/li_producer_theta_gamma_density_comparison_attack.md,
528lines/SHA7bd08cc114c06b36e068b42339a4d176adfde463045ca8842de095d8f3ccbd65,
unchanged. Its complete-source identities, normalization, CDF reserve,
matched unequal-mass transport, marked real-time CP coupling and endpoint
derivative admissions are reused, not relabelled as new results.

## 1. Literal source, domains, and complete admissions

Write w_q=(xiSpectralPoint q)^(-1), q:XiZeroCopy, including EVERY analytic
multiplicity copy; u_q=|Re w_q|, v_q=|Im w_q|. Put A=xiShiftAbsoluteMass 0,
gamma=1/300, rho=1/sqrt150, M_j=normalizedPrimeArchMoment j. The literal
single-Xi primitive is

  P(t)=liEvenCrossActualClockPrimitive(t)
      =sum_q Re(1-cos(t w_q))
      =sum_q [1-cos(u_q t)cosh(v_q t)].                    (I1)

No half-copy divisor or factor1/2 occurs in I1. Source atoms obey

  sum_q |w_q|^2=A<infinity, A>0,
  |w_q|^2<1/150, v_q<gamma, u_q>v_q, u_q>0.              (I2)

Indeed alpha=xiSpectralPoint q has |Im alpha|<1/2 and
(Re alpha)^2>599/4. Inversion divides both coordinates by |alpha|^2,
so |Re w|>|Im w|. The last inequality is independent of RH.

Let beta=sup_q v_q. All-copy squared summability gives finite positive
upper levels. Consequently either beta=0, or beta>0 is attained, its
complete fiber Q={q:v_q=beta} is finite/nonempty, and there is
0<=beta2<beta bounding every complementary copy. Thus

  0<=beta<gamma; beta=0 iff RH.                           (I3)

The beta=0/RH case does NOT assert Q finite. Finite maximal packet/gap is
used only when beta>0. I3 is source geometry, not an assumed zero-free disk.

On t>=0 the complete primitive satisfies

  |P(t)| <= (A/2)t^2 exp(beta t).                         (I4)

Proof: the atom bound |1-cos(tw)|<=(t^2/2)|w|^2 exp(t|Im w|)
followed by the full norm-summable sum. The same proof gives compact
majorants before EVERY integral/sum below. For any REAL a and T>0 define

  D_a(T)=integral_0^T exp(-a t)P(t)/t dt.                 (I5)

The integrand extends continuously by zero at0, since P(t)=O(t^2).
Every finite cutoff is genuine L1, and Fubini gives

  D_a(T)=sum_q G(u_q,v_q;a,T),
  G(u,v;a,T)=integral_0^T exp(-a t)
                    [1-cos(ut)cosh(vt)]/t dt.            (I6)

Absolute integrated atom norms are bounded by
(A/2) integral_0^T t exp((beta-a)t)dt. This admits all copies, both
transverse signs, the origin and the full cutoff; no first-power sum.

For a>beta, I4 gives genuine signed L1, all polynomial weights, and

  H(a)=integral_0^infinity exp(-a t)P(t)/t dt
      =log Phi(1/a)>0.                                  (I7)

Here Phi(z)=XiC(-I*z)/XiC(0)=sum_j nu_j z^(2j)/(2j)!,
nu_j=thetaCuspNormalizedEvenMoment j, nu_0=1, nu_j>0 for j>0.
I7 extends the already audited P9/P10 proof from a>gamma to a>beta:
I4 supplies all its absolute P admissions on that larger domain. The
actual integrated Volterra law is P+P*K=tK, K=B_theta', obtained by compact
integration by parts from F*B_theta=tB_theta'. Absolute Laplace Fubini
applies to P*K; positive full-series Tonelli gives
Khat(a)=Phi(1/a)-1 and (tK)hat(a)=Phi'(1/a)/a^2.
The resulting Phat=Phi'(1/a)/(a^2 Phi(1/a)) implies H'=(log Phi(1/a))'.
Both vanish at infinity by dominated convergence and Phi(0)=1. This
retains factor ONE and the literal single normalized Xi. It uses neither
RH nor a log branch across a complex zero nor an outside-strip integral
for eta. No absolute endpoint transform at a=beta is claimed.

For the Gamma-row construction retain p>rho. The full signed density
sigma_p(t)=exp(-pt)P(t)/t on t>0, zero elsewhere, equals tau_p^+-tau_p^-.
These are the same complete coefficient-split Gamma(2j,rate p) measures
as the baseline528; they are not the continuous density's Jordan parts.
The baseline's signed L1/TV, all moments and actual log-law coupling
remain in force. No wider convergence premise is silently added to its
43 future formal contracts.

## 2. A sharper actual cutoff theorem, without a Gamma-row budget

Claim I8: if u>=v>=0, u>0, and a>=v, then G(u,v;a,T)>0 for EVERY T>0.
This is the scalar admission; it is applied only to the literal atoms I2.

First, for b>=0,u>0,

  S_b(u,T)=integral_0^T exp(-bt)sin(ut)dt >=0.            (I8a)

For b=0 this is (1-cos(uT))/u. For b>0 exact integration gives
[u-exp(-bT)(b sin(uT)+u cos(uT))]/(b^2+u^2).
Set f(T)=exp(-bT)(cos(uT)+(b/u)sin(uT)). Then
f'=-(b^2+u^2)exp(-bT)sin(uT)/u. On successive half periods its maxima
are f(2k*pi/u)=exp(-2kb*pi/u)<=1, starting at f(0)=1.
Thus f(T)<1 for T>0 when b>0. This proves I8a, including the undamped
endpoint, with no assertion that sin has pointwise positive sign.

Differentiation under the finite compact integral gives

  dG/du = (S_(a-v)(u,T)+S_(a+v)(u,T))/2 >=0, a>=v.       (I8b)

Finite parameter-local domination is elementary: the differentiated
integrand exp(-at)sin(ut)cosh(vt) is continuous at0. Thus it is enough
to prove the diagonal u=v>0. v=0 is separate: integrand 1-cos(ut)>=0,
positive on a nonempty interval next to0, so its cutoff integral is strict.

Diagonal baseline a=v>0 scales to

  G(v,v;v,T)=g(X), X=vT,
  g(X)=integral_0^X [exp(-x)-(1+exp(-2x))cos x/2]/x dx.  (I8c)

For 0<x<pi/2, cos x cosh x<1: derivative of its logarithm is
tanh x-tan x<0, since tan x>x>tanh x. At pi/2 cosine is0.
On [pi/2,3pi/2] cosine<=0. Hence g(X)>0 for 0<X<=3pi/2.
The origin causes no singularity: the numerator is O(x^4).

For large X, the exact conditionally convergent total is

  g(infinity)=log5/4.                                  (I8d)

Admission: for a>v the ordinary absolutely convergent Frullani calculation
gives
G(u,v;a,infinity)=1/4 log([((a-v)^2+u^2)((a+v)^2+u^2)]/a^4).
At u=v=1 let a decrease to1. The finite-cutoff integrals converge by
compact domination; their tails converge uniformly because
|integral_X^infinity exp(-bx)cos x/x dx|<=2exp(-bX)/X for ALL b>=0,
while the nonoscillating tail is <=exp(-aX)/(aX).
The b=0 integral is admitted by Dirichlet, not claimed absolute.
Thus the limiting full total is log5/4. The cosine-tail bound follows
by integration by parts with sin x: its boundary plus derivative-weight
integral are each at most exp(-bX)/X. This also proves convergence.

Consequently, for X>=3pi/2>9/2,

  g(X)>=log5/4-[exp(-X)+1+exp(-2X)]/X
       >1/3-47/165=8/165>0.                             (I8e)

Constants: exp(-X)<=1/(1+X)<=2/11 and exp(-2X)<=1/(1+2X)<=1/10;
the bracket divided by X is <=(2/11+1+1/10)*(2/9)=47/165.
log5>4/3 follows by differentiating
log y-2(y-1)/(y+1): derivative (y-1)^2/[y(y+1)^2]>0 on y>1.
No decimal bounds or numerical sampling occur.

Finally let a>=v and d=a-v. Integration by parts of the ALREADY-POSITIVE
diagonal primitive, not of a positive integrand, gives

  G(v,v;a,T)=exp(-dT)g(vT)
                +d integral_0^T exp(-dt)g(vt)dt >0.      (I8f)

Together with I8b this proves I8 for every cutoff. Equality a=v is
included; the origin and v=0 were handled separately.

Apply I8 to I6. Nonempty XiZeroCopy and full absolute summability yield

  D_a(T)>0 for EVERY T>0 and EVERY a>=beta.              (I9)

In particular a>=gamma is an unconditional explicit admissible domain,
far wider than the earlier geometric reserve threshold a_* >rho.
I9 is NEW source-sign progress: it uses each actual spectral atom's
u_q>v_q and a>=v_q; it does not assume all M_j signs. The budget528 still
provides its explicit Gamma2/second-row margin on its own narrower domain.
The scalar intermediate does not substitute an arbitrary source for Xi.

## 3. Exact boundary: below beta the same source is negative cofinally

Assume beta>0 and ANY REAL a<beta; put d=beta-a>0. Use the COMPLETE finite
top fiber Q and complementary bound beta2<beta from I3. On s>=1,

  P(s)=card(Q)-[exp(beta s)+exp(-beta s)]
                          sum_(q in Q)cos(u_q s)/2 + P_compl(s),
  |P_compl(s)|<=(A/2)s^2 exp(beta2 s).                  (I10)

This is the exact absolutely convergent all-copy split. Prefix0..1 is
kept as the original signed integrable expression; divergent isolated
1/s terms are NEVER extended to0.

For a fixed u and d>0, elementary complex integration by parts shows

  T exp(-dT) integral_1^T exp(ds)cos(us)/s ds
      =Re(exp(iuT)/(d+iu))+o(1), T->infinity.            (I11)

The primitive is exp((d+iu)s)/(d+iu); the remainder is
(d+iu)^(-1) integral_1^T exp((d+iu)s)/s^2 ds.
After multiplying by T exp(-dT), split at T/2: the first part is bounded
by T exp(-dT/2)/|d+iu|; the second by 4/[d|d+iu|T]. Both vanish.
The lower boundary also vanishes. This proves I11, not a heuristic
endpoint approximation. It works for u of either sign.

All other parts in I10 vanish after the SAME scaling T exp(-dT):
the constant term is bounded by a polynomial times exp(max(-a,0)T),
the negative-beta branch by a polynomial times exp(max(-beta-a,0)T),
the complement's integrated bound by a polynomial times
exp(max(beta2-a,0)T), and the original finite prefix is constant.
Each displayed exponent is STRICTLY below d (beta>0,beta2<beta,a<beta).
For a nonpositive integrated exponent use the simple bound integral_1^T
s exp(ks)ds<=T^2 when k<=0; for k>0 use <=T^2 exp(kT).
This covers beta2-a=0 and negative a explicitly; no missing tail case.

Simultaneous phase recurrence on the finite multiset Q supplies T_n>=n+1,
T_n->infinity, and exp(i u_q T_n)->1 for EVERY q in Q. Absolute values
in u_q are harmless since the same recurrence handles signed Re w_q;
its conjugate also tends to1. I11, finite summation, and the full gap yield

  T_n exp(-(beta-a)T_n) D_a(T_n)
    -> -(1/2) sum_(q in Q) (beta-a)/[(beta-a)^2+u_q^2] <0. (I12)

Every multiplicity copy contributes separately. The coefficient is NOT
-card(Q)/2; damping changes each denominator. Positivity of beta-a,
finiteness/nonemptiness of Q and positive denominators prove strict sign.
Because exp((beta-a)T_n)/T_n->infinity, I12 implies

  D_a(T_n)->-infinity.                                  (I13)

Thus for a>=0, without assuming either RH branch,

  [for every T>0, D_a(T)>=0] iff a>=beta.                (I14)

If beta=0, RH makes every atom 1-cos(u_q t) nonnegative, so D_a(T)>0
for EVERY REAL a and T>0; beta=0 needs no finite top packet. If beta>0,
I9/I13 give the sharper ALL-REAL classification: cutoff positivity iff
a>=beta. The negative branch is conditional on a<beta, NOT an assertion
that actual beta>0 or that an actual negative cutoff is currently known.

## 4. Marking cone, exact inversion, and its endpoint

Fix p>rho and r>0, a=p-r. Every finite signed mark is well-defined by
the baseline complete TV admission and probability Exp_r. Signed Fubini
gives its exact continuous positive-axis density

  kappa_(p,r)(t)=r exp(-rt)D_(p-r)(t).                  (I15)

It has zero mass/density on the negative axis and no atom at0; near0 it
is O(t^2). Its total signed mass is H(p)>0, independently of r. If beta>0,

  kappa_(p,r)>=0 everywhere iff 0<r<=p-beta,             (I16)

with strict positivity on t>0 in the admissible range. Outside the range,
I12 gives the stronger literal asymptotic

  T_n exp((p-beta)T_n) kappa_(p,r)(T_n)
   -> -(r/2) sum_(q in Q)(beta-p+r)/[(beta-p+r)^2+u_q^2]<0. (I16a)

Thus kappa has negative values cofinally; it need not diverge negatively
because p>rho>beta. If beta=0, RH gives kappa>0 on t>0 for ALL r>0.
This is a source-derived classification of a genuine marked signed law,
not a generic counterinput. Its use as an RH criterion is not an RH proof.

On the strict interior a>beta the marked Laplace function
h_(p,r)(s)=rH(p+s)/(r+s), s>=0, has ALL strict compensated signs:

  (-1)^n h^(n)(s)=integral_0^infinity t^n exp(-st)kappa(t)dt>0,
  sum_(k=0)^n (r+s)^k(-1)^k H^(k)(p+s)/k! >0.          (I17)

The same conclusion holds at a=beta, because I9 gives pointwise positive
kappa and complete Gamma-row/Exp convolution gives every polynomial L1.
Endpoint s=0 ordinary derivatives follow from the baseline's exponential
moment with 2epsilon<min(r,p-rho). This uses p>rho, not a>rho.
When beta=0, the same genuine moment argument and positive kappa extend
I17 to every r>0, including a<0; this is the conditional RH branch.

Conversely, if beta>0 and r>p-beta, choose T0 with kappa(T0)<0 from
I16a. kappa is bounded/continuous: |sigma_p(t)|<=(A/2)t exp(-(p-beta)t)
and convolution with a probability exponential preserves boundedness.
The Gamma density of shape n+1/rate n/T0 is an approximate identity at
T0 (mean T0(1+1/n), variance T0^2(n+1)/n^2). Chebyshev plus bounded
continuity gives its kappa average ->kappa(T0)<0. Hence some moment
integral t^n exp(-s_n t)kappa(t) is negative, s_n=n/T0>0. Therefore I17
cannot hold for all n AND all s in this forbidden range. This explicitly
tests the full compensated cone, not merely finitely many protected signs.

The exact inverse on t>0 is

  kappa'+r kappa=r exp(-pt)P(t)/t.                      (I18)

Full differentiation is ordinary FTC applied to continuous D_a'.
Marking is INJECTIVE (its Laplace multiplier r/(r+s) never vanishes for
s>=0); its complete data determines sigma_p. What positivity supplies is
only kappa>=0, not kappa'+r kappa>=0. The latter is the literal missing
source inequality. I16 shows why taking allowed marks toward their
boundary does not provide an approximate identity at fixed p: r tends
to the FINITE p-beta. Unbounded positive rates at this fixed p are
equivalent to beta=0, already RH by actual source geometry.

The old geometric threshold a_*=sqrt((1+A/(2M0))/150) was only a reserve
method boundary. Letting a down to a_* makes its explicit delta(a) vanish
and leaves r=p-a_* finite. New I9 reaches the genuine source boundary
beta, including its endpoint, but still cannot drive r to infinity when
beta>0. No threshold from the old43 formal contracts is altered.

Nor does p,r->infinity with fixed a>=beta remove the marking:

  exp(pt) kappa_(p,r)(t)/r
      =exp(at)D_a(t)
      =integral_0^t exp(a(t-u))P(u)/u du.                (I19)

The right side is INDEPENDENT of r. Increasing r while changing p does
not localize the actual undamped source. This is an exact actual-family
failure of that proposed limiting mechanism, with no arbitrary sequence.

## 5. Stronger positive survivor: exact pole and all-order remainder

Take p>rho,r>0,a=p-r>beta, d=a-beta>0,q=p-beta=r+d.
Use I7 and I4 to retain the COMPLETE signed tail:

  D_a(t)=H(a)-Tail_a(t),
  |Tail_a(t)| <= (A/2)exp(-dt)[t/d+1/d^2].              (I20)

Thus the literal marked density has a positive leading exponential and
a genuinely signed faster remainder R:

  kappa(t)=rH(a)exp(-rt)+R(t),
  |R(t)| <= (Ar/2)exp(-qt)[t/d+1/d^2].                (I21)

Both use the full actual P, not isolated divisors. In particular
exp(rt)kappa(t)->rH(a)>0. For EVERY n>=0 its genuine signed moment m_n
satisfies the explicit complete error

  |m_n-H(a)n!/r^n|
   <=(Ar/2)[(n+1)!/(d q^(n+2))+n!/(d^2 q^(n+1))],
  r^n m_n/n! -> H(a)>0.                               (I22)

Integrating I21 with t^n proves the bound; q>r makes the normalized error
O(n(r/q)^n). This is an all-order actual source result, not a protected
finite-order calculation. More generally for EACH fixed s>=0,

  (r+s)^(n+1)/(r n!)*(-1)^n h^(n)(s)->H(a),
  sum_(k=0)^n (r+s)^k(-1)^kH^(k)(p+s)/k! ->H(a).        (I23)

Replace r,q by r+s,q+s in the same integrals; the explicit error is
<= A(r+s)/2 *[(n+1)/(d(q+s)^2)+1/(d^2(q+s))]
                       *((r+s)/(q+s))^n ->0.
The second equality uses the exact Leibniz coefficient from I17, not an
extra Tauberian step. It explains positive compensated high orders from
the SAME positive pole, with genuine all-order source/error admissions.

The inverse I18 kills that pole EXACTLY:

  R'+rR=r exp(-pt)P(t)/t.                              (I24)

All information about unsmoothed sign is in this correlated derivative
remainder. A small relative value bound in I21 gives no sign to I24;
there is no derivative estimate of useful sign supplied by I20/I21.
If actual beta>0, the already-proved primitive negative sequence shows
I24 negative somewhere despite I21 and strictly positive kappa. This is
a conditional SAME-SOURCE obstruction, not an unconditional counterexample.
The marked pole masks exactly the slower signed reciprocal oscillation
that inversion exposes. Removing the pole numerically or algebraically
does not remove that sign burden.

## 6. Composition and exact probability-law scope

For a certified first mark, convolve with any finite list of positive
Exp_(r_i) measures. Positive forward closure holds; total mass stays H(p).
The full signed/positive convolution is genuine L1 by Fubini. Its Laplace
function is H(p+s) product_i r_i/(r_i+s). The original sigma_p is recovered
on positive t by product_i(D+r_i) divided by product_i r_i, with the
distributional zero-boundary terms retained. No such differential inverse
has been proved positive on this actual marked cone. All exact data is
retained, but the available positive test cone is smoother/smaller.

At each certified stage the positive difference intensity gives full
REAL-time compound-Poisson coupling by genuine convolution exponential:
CP(v marked_tau+)=CP(v marked_tau-)*CP(v marked_difference), v>=0,
including an independent product realization. These are the BASELINE
marked probability laws, possibly marked again. Their Laplace exponents
contain the product multipliers and are NOT the original actual mu_p's
exponent H(p+s)-H(p). No integer-time-to-fractional-divisibility inference
or law cancellation with a positive inverse is made.

## 7. Attempted additional theta restoration and exact open admission

Actual positive nu_j, genuine entire Phi, the actual Ward/cumulant
recurrences and full spectral source bounds were retained. They supplied
H(a)>0, I2/I4, the complete L1 domain and the sharper I9. The actual
Laplace identity fixes the positive pole in I21. None of these signs
controls R'+rR. The complete Ward raw-to-log recurrence still contains
its signed convolution subtraction; dropping it would change the same
genuine P whose primitive receiver is already known.

Concrete attempted restoration: require the marked density's hazard-type
one-sided differential inequality

  [exp(rt)kappa(t)]' >=0 for EVERY t>0,
  equivalently exp(rt)(R'+rR)>=0.                       (I25 OPEN)

This would orient P, but is NOT renamed as an independent proved source
law. In fact it is precisely D_a'(t)=exp(-at)P(t)/t>=0. Our atom theorem
proves D_a>0, not monotonicity; individual integrands have oscillating
cosh-cos sign. I12 proves source-level cofinal negative D_a below beta,
and the actual primitive negative escape under notRH rules out I25
even within the admissible marked cone. No all-source inverse estimate
was obtained that bypasses this correlation. At fixed p the maximal
positive marking range and its endpoint are now exact, rather than an
artifact of a geometric coefficient budget.

Outcome: NEW positive cutoff/marking/compensated-sign classification and
full leading-pole/all-order error are paper proved here; independent audit
is required. Unsmoothed N17 and the actual raw-to-log correlation I25
remain OPEN. No unconditional RH conclusion, world novelty, route retirement or formal
completion is claimed. No further source-general inverse obstruction is
asserted beyond the exact actual-family limits and classification above.

## 8. Exact primary source/dependency ledger

All paths below are real files under formal/GaloisForLFunctions/RHTower,
unless explicitly /tmp. Relevant bodies were source-read, including fresh
checks in this task; previous full audits are reused only where unchanged.
No inaccessible private declaration is proposed as an existing public API.

|Claim/admission|Exact primary anchor and scope|
|---|---|
|Literal all-copy primitive I1|LiEvenCrossActualClockPrimitive.lean:23 definition; :151 liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine; :114 summable_norm_liEvenCrossActualClockCosineAtom. Full complex reality/FTC, no sign premise.|
|Atom compact squared bound|LiEvenCrossActualClockPrimitive.lean:46 private primitive_cosine_bound_nonneg, :85 private primitive_complex_bound; sourcechecked proofs use actual LiClockSineImaginaryEnvelope, not first-power summability. Public abs bound :196 abs_liEvenCrossActualClockPrimitive_le uses gamma. I4 adapts same proof with beta as a new paper result.|
|Complete mass, all-tail admissions|PrimeArchValuationSectorCones.lean:31 xiShiftAbsoluteMass, :34 summable_xiShiftAbsoluteMass, :45 xiShiftAbsoluteMass_pos; XiReciprocalSquareSecondMomentRadius.lean:30 norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty; :115 abs_normalizedPrimeArchMoment_add_le_secondMomentRadius. Full-copy normalization, no presumed M_j signs.|
|u>v, nonzero real frequency|XiReciprocalSquareSecondMomentRadius.lean:52 oneHundredFifty_lt_norm_xiSpectralPoint_sq; :66 fiveHundredNinetyNine_fourths_lt_xiSpectralPoint_re_sq. Literal strip via xiSpectralPoint_im_mem_openHalf. Inversion preserves absolute coordinate ratio.|
|Uniform explicit gamma bound|LiEvenCrossActualClockDampedResolvent.lean:27 abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred; :81 norm_liEvenCrossActualClockResponse_le_mass_mul_exp. New CDF proof uses actual v, not an assumed RH strip.|
|Full beta/top/gap|LiEvenCrossActualClockTopFrequency.lean:95 liEvenCrossActualClockReciprocalGrowthRate; :99 TopPacket; :107 summable_liEvenCrossActualClockReciprocalGrowthRate_sq; :116 finite_liEvenCrossActualClockReciprocalGrowthRate_ge; :142 exists_liEvenCrossActualClockTopPacket_of_not_rh. Whole final block94–155 read. No finiteness claim at beta0.|
|Complete simultaneous phases|LiClockFiniteTopSinePacket.lean:88 exists_liClockFiniteTopSinePacket_negative_limit; its complete body101–127 explicitly calls exists_simultaneous_phase_recurrence and proves each exp(iT Rew)->1, cos->1,sin->0. I12 is a NEW integrated-packet asymptotic, not obtained by integrating a sequence-only limit.|
|Exact split and complement|LiEvenCrossActualClockPrimitiveNegative.lean:104 private pn_norm_complement_le; :169 private pn_source_split. Bodies freshly read; I10 reproves their mathematical split/bound, not a Lean access claim. Public :191 exists_liEvenCrossActualClockPrimitive_negative_escape_of_not_rh; :251 liEvenCrossActualClockPrimitive_rh_criteria retain conditional scope.|
|Actual all-positive raw theta and Phi normalization|LiEvenCrossActualClockBorelSource.lean (whole previously audited source), PrimeArchThetaAllOrderCumulant.lean:39–47 and PrimeArchThetaCumulantMinor.lean:439–460 as pinned in final291/final475. These give single normalized Xi/Phi, not a squared source.|
|Actual Volterra factor ONE|LiEvenCrossActualClockVolterra.lean:241 liEvenCrossActualClockResponse_volterra_eq_mul_deriv. Full original source proof previously audited, exact final header freshly verified. /tmp/li_root_integrated_clock_source_boundary.md:P4 gives P+P*K=tK with K=B_theta'. P9/P10 sourceproof100–123 freshly read. I7 extends only its genuine damping domain using I4, not its normalization.|
|Full original Gamma rows and CP laws|Unchanged528 D1–D20 and unchanged475 N10–N15. p>rho retained for coefficient-split tau±. Every new marking statement names these same intensities and explicitly keeps that domain.|
|Inverse I18 / leading I20–24|NEW elementary FTC and complete signed tail integration from I4/I7, with all n factorial Gamma integrals derived directly by repeated integration by parts. No proposed installed theorem is asserted.|
|Scalar I8 / integrated packet I11–13|NEW complete proofs above. Prospective formalization would require toolchain probes and full paper/independent gates; no Lean file/theorem exists by this note.|

Important correction made during author self-audit before freeze: the
integrated law is P+P*K=tK, NOT P*B_theta=tB_theta. I7 now uses the exact
P4 law and Khat=Phi-1 throughout. All subsequent transforms use this
correct factor/normalization. No frozen paper/source was changed.

## 9. Every returned hit: applicability and overlap

The complete 61-record deep retrieval was inspected, including all source
methods/proof excerpts. Index/provenance remains as recorded at start.
Disposition abbreviations: admission=valid source/analytic bound only;
prior=known coupling/source machinery; mismatch=different literal object;
finite=finite-order statement, not all-order inverse comparison.

Candidate20 (same source order):

|Index|Exact returned declaration|Disposition|
|---|---|---|
|C0|ThetaSourceWard.thetaSource_shiftPair_decay|Generic supplied exponential decay; admission, no positive density inverse.|
|C1|ThetaExpDecaySource|Supplied decay Prop; cannot serve as orientation.|
|C2|thetaCuspFullSource_le_tiltDecayConstant|Actual theta envelope; admission only.|
|C3|thetaGaussianScore_firstAtomDecay_le|First-atom envelope, no full signed Gamma comparison.|
|C4|decay_half_of_theta, formal/tmp/l46/A.lean|Supplied source envelope; different half-decay goal.|
|C5|decay_half_of_theta, ThetaRigidityHardyEqualityCase|Same supplied envelope; not inverse positivity.|
|C6|HedenmalmThetaSource.intervalMass_le_exp|Actual interval mass bound; admission only.|
|C7|HTGeometry.convPow_compoundPoisson|Prior genuine integer-time semigroup, not unmarking.|
|C8|criticalCumulative, PolarPrimeMellinDefect|Different arithmetic cumulative observable.|
|C9|HTGeometry.laplace_compoundPoisson|Prior finite-intensity Laplace law.|
|C10|HTGeometry.logLaplace_compoundPoisson|Prior law; installed logLaplace is NEGATIVE log.|
|C11|HedenmalmThetaSource.abs_thetaCuspFullSource_le|Actual source decay admission only.|
|C12|HTGeometry.compoundPoisson|Prior definition, no actual signed inverse.|
|C13|thetaCuspTiltDecayConstant|Actual envelope constant definition.|
|C14|d4ThetaHawkingEKGChiralCuspL2DecayRate|Different mode/physical carrier.|
|C15|ProbabilityTheory.avgRisk_fintype|Statistical averaging, wrong kernel/source.|
|C16|SemilocalProlateHyperbolicPoissonSource.sourceResolvedPoissonMatrix|Semilocal matrix Poisson, not Gamma jump density.|
|C17|ProbabilityTheory.avgRisk_const_of_fintype|Statistical carrier, mismatch.|
|C18|ProbabilityTheory.avgRisk_le_iSup_risk|Statistical carrier, mismatch.|
|C19|ProbabilityTheory.cdf_gammaMeasure_eq_lintegral|Prior Gamma CDF identity, useful for old budget; no inverse sign.|

SourceArgument20, INCLUDING all supplied methods/proof excerpts:

|Index|Exact declaration|Disposition|
|---|---|---|
|S0|l2Amplification_primeCoordinate_actualThetaPacket|Actual tensor prime-coordinate norm, wrong clock/observable; previously exact-premise-audited.|
|S1|HTGeometry.gomesQubitOrbitDerivative|Qubit orbit, mismatch.|
|S2|quantumStratonovichCayleyTransition_theta_eq|Different quantum transition.|
|S3|HedenmalmThetaSource.thetaSourceSignedStageCorrection|Finite theta operator stages, not full P marking.|
|S4|HTGeometry.gomesQubitOrbitBias|Different qubit coordinate.|
|S5|thetaCuspComplexSource|Actual source cast, admission only.|
|S6|thetaCuspFullLogJetEight|Finite derivative order, not uniform log/inverse sign.|
|S7|thetaCuspFullLogJetSix|Same finite-order limitation.|
|S8|HedenmalmThetaSource.thetaSourceSignedStageFinMatrix|Different finite-matrix signed source.|
|S9|HTGeometry.gomesSSHCarrier|Different physics carrier.|
|S10|HedenmalmThetaSource.thetaSourceSignedStageMatrix|Different operator-stage source.|
|S11|HTGeometry.gomesFockPhase_vector_moments|Unitary gauge invariant Fock moments, mismatch.|
|S12|HTGeometry.gomesFockZeroPhase_vector_moments|Same mismatch.|
|S13|thetaBilateralLaplace|Actual bilateral theta transform, source admission; not positive unmarking.|
|S14|liEvenCrossActualClockBorelCoefficient|Actual nu/factorial definition, prior exact source.|
|S15|HTGeometry.egbFixedCharge_enthalpy_jump|Different thermodynamic quantity.|
|S16|continuous_thetaCuspSourceTerm_one|Actual first atom continuity, admission only.|
|S17|thetaCuspSchwartzReal_apply|Actual Schwartz representative, admission only.|
|S18|ccmLocalPotentialLocalizationDefect_eq|Actual Weil IMS/localization, wrong quadratic source; ready method does not fix mismatch.|
|S19|ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular|Finite eighth-order actual identity, not all inverse orders.|

Prose10, every full passage read:
P0 theta-compact-inverse-zero-jordan-history:2179; P3 same:1688:
original Schwartz compact-core/tempered signed jets, different inverse.
P1 stage-two-recursive-unconditional-formalization:3042; P2:2720;
P4:3662; P6:5001; P7:3304: compact division/localization and durable
certificate metadata, no actual marked density sign. P5
jas-critical-singleton-prime-multiplication-escape:1 and P9
jas-actual-theta-grade-norm-escape:1 concern different tensor grading/
source sewing obstructions. P8 theta-c5-d1-source-slope-corridor:1 is an
OPEN actual finite-log-jet corridor; no proved all-order log positivity.

LeanPassage10, every returned source/body interval read:
T0 GomesFockQubitGauge:1–77 and T2:73–149: gauge invariance, mismatch.
T1 HedenmalmThetaActualFiniteDivisorRigidity:1–72: conditional actual
finite real-divisor receiver, not signed jump inverse. T3
GomesQubitOrbitTransport:1–90: different full Gibbs plane. T4
CCMThetaArithmeticLocalization:165–179: exact restricted Weil IMS,
different source. T5 SkewAdjointGreenSquare:1–89: finite matrix PSD
inverse square, no analytic actual comparison. T6
CayleyDefectDynamicalVisibility:1–86: already-POSITIVELY marked Cayley
atoms; cannot supply positivity to this signed source. T7
FokasLenellsRegularPositiveWeight:1–89: different nonlinear scattering
compatibility. T8 SchwartzCompactPolynomialSeparation:219–324:
positive pointwise polynomial multiplier/inverse, different topology and
operator. T9 ConstitutivePositiveFormationReflection:100–143: finite
positive-matrix recovery, not positive differential inverse of kappa.

Ingredient1's proposed ThetaDecay+IntervalMass+shiftPair chain consists
of valid decay admissions for its own supplied source, not the literal
Gamma density or I25. It is proposed/unverified and does not prove this
target. Retrieval's sufficient-sources assessment is rejected on exact
observable grounds, not accepted as a mathematical proof.

Targeted direct lexical followup, after this mechanism was selected:

    python3 scripts/formal_tools.py research '"cosh" "primitive"' --mode lexical --no-refresh --json

Session56933 terminal0. ALL9 eligible displayed declarations read:
integral_cosh_interval (PoleKreinNyquistTrace); two
abs_integral_cosh_mul_autocorrelation{,_full}_le (HalfLineCoshPrimitive);
tentPrimitive (TentTransformAmplitude); hasDerivAt_polarCosinePrimitive
(CCMPolarPrimeSourceSign); continuous_expShiftPrimitive and
expShiftPrimitive (CoshHalfPowerLowerBound);
exponentialSourceCombination_primitive_pairing (SignedCharFunCentralJet);
integral_weilAtomSymbol_dirichlet_odd (WeilPositivityImaginaryQuadraticConductorLaw).
Total27 raw matches,7modules,9eligible after per-module cap2; no other
returned arrays/markers/exploration. No coverage/compiler freshness
metadata was reported by this lexical result. The two relevant primary
bodies HalfLineCoshPrimitive:75–99/122–145 and CCMPolarPrimeSourceSign:59–82 were
freshly read: the former ASSUMES a growing primitive bound; the latter
is an exact undamped polar primitive derivative. Neither instantiates
the truncated damped logarithmic primitive I8. The remaining displayed
contracts have different observables. This is bounded inspected overlap,
NOT exhaustive corpus absence or world novelty.

## 10. Author full-claim self-audit and remaining status

I1–I7: full Xi copies, actual ratio geometry, attained positive top with
strict full complement gap; genuine cutoff L1 and origin; full theta
Phi/Volterra factor ONE; signed improper domain ONLY a>beta.
I8a–f: all damping endpoints, v0/u>0, finite parameter differentiation,
conditional b0 Dirichlet tail, Frullani limit and explicit47/165 fence;
higher damping acts on an already-positive cumulative, not its integrand.
I9: absolute full sum and nonempty strict term; no M_j global sign.
I10–13: exact top splitting only after1, all-copy complement bound,
integration-by-parts asymptotic, simultaneous complex phases, EVERY
exponent subcase and negative normalized limit implying atBot.
I14–16a: beta0 top not finite, RH case separated; real negative a allowed
only where explicitly proved; p>rho for full Gamma marked laws.
I17: all n and s>=0 including ordinary endpoint differentiability;
converse uses normalized Gamma localization of actual negative kappa,
not a hypothetical sequence or finite-order protected sector sign.
I18–19: inverse FTC and finite maximal mark range; input changes when
p changes; exact undamping identity blocks the proposed approximate limit.
I20–24: full signed tail, distinct p/a/beta/r/q, complete factorial moments,
all-order normalized error and exact annihilation of positive pole.
I25: remains OPEN/RH-bearing source correlation; neither marking nor
Ward/positive raw coefficients supplies it. Probability CP uses actual
marked intensities only; original mu and negative-log convention retained.

All61 deep/all9 displayed lexical items processed; source freshness
qualified; no new Lean claims. Only this authorized MD was written.
No compiler, numerical job, new agent, tree/card/source edit or route
retirement. New source theorems above are PAPER claims awaiting independent
audit, not installed Lean exports. Strongest positive survivor is I9/I14/
I16/I17 plus exact I21–23; unsmoothed N17 remains OPEN.
