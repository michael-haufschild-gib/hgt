# PW-B pairing forced by the two actual jump directions

- **ID:** PW-B-GAMMA-REVERSIBLE-PAIRING-2026-09-11
- **Stage:** 1-in-progress
- **Status:** Reversible density, uniqueness, source weight, Jacobian, literal cutoff contact, actual source-mode defect and its exact logarithmic pairing are Lean-closed. Complete high-order source-moment recovery and the moment-series divergence obstruction are also Lean-closed. Original-cutoff extraction, full adjoint, source domain and spectral occurrence remain open.
- **Objective:** Derive the positive pairing and retained adjoint correction from the existing forward and inverse-gain reflected source generators, then test their actual arithmetic domain.

## Actual source and candidate pairing

The existing Frullani and reflected-Frullani modules prove, for x>0,
Q(x)=sqrt(x)*exp(-x), Rf(x)=Q(x)*f(1/x)/Q(1/x), and

`T_h f(x)=exp(-h)*Q(x)*(f(x+h)/Q(x+h))`,

`R T_h R f(x)=exp(-h)*Q(x)*(f(x/(1+h*x))/Q(x/(1+h*x)))`.

Thus in the normalized coordinate g=f/Q the two complete generators are

`A g(x)=integral_0^infinity exp(-h)*(g(x+h)-g(x))/h dh`,

`B g(x)=integral_0^infinity exp(-h)*(g(x/(1+h*x))-g(x))/h dh`.

Every occurrence of these expressions requires admission of the complete
increment. The separate gain and loss rates diverge at h=0.

For 0<x<y the opposite jump densities, including the reciprocal Jacobian,
are

`k_plus(x,y)=exp(-(y-x))/(y-x)`,

`k_minus(y,x)=(y/x)*exp(-(1/x-1/y))/(y-x)`.

Set w(x)=exp(-x-1/x)/x. Direct multiplication gives

`w(x)*k_plus(x,y)=w(y)*k_minus(y,x)=exp(-y-1/x)/(x*(y-x))`.

If another density rho satisfies every such pair balance, dividing its
identity by this strictly positive identity gives rho(x)/w(x)=rho(y)/w(y).
Comparison with x=1, treating both orders, makes the ratio constant on
the positive ray. A positive density has a positive constant ratio.
This determines the pairing up to scale within the stated class; it
does not derive a physical selection principle requiring that class.

The inversion law is w(1/x)/x^2=w(x). In the original f coordinate its
density is eta(x)=exp(x-1/x)/x^2, since eta(x)*|Q(x)|^2=w(x).
Changing to x=exp(t) yields eta(exp(t))*exp(t)=pwLogSingularGain(t).
The candidate is therefore the existing singular source geometry.

The density itself is integrable: (1/x)*exp(-1/x)<=1 gives
w(x)<=exp(-x) on the positive ray. Higher nonnegative integer moments
are bounded by admitted Gamma moments; negative moments follow from
inversion, after proving the measure-change identity.

## Retained cutoff correction

Pointwise balance does not justify A*=B. At target x, a forward cutoff
y-x>delta becomes the reflected cutoff h>delta/(x*(x-delta)), for
0<delta<x. Its difference from the native reflected cutoff is

`integral_[delta/(x*(x-delta)),delta] exp(-h)/h dh`.

Split the integrand as 1/h+(exp(-h)-1)/h. The first integral equals
log(x*(x-delta)), tending to 2*log(x). The second tends to zero: its
complete integrand is bounded near zero and both endpoints tend to zero.
This paper calculation predicts A*=B+2*log(x) and B*=A-2*log(x) on
an appropriate common domain. Their sum should be symmetric, with
negative quadratic form

`-integral_{0<x<y} exp(-y-1/x)/(x*(y-x))*|g(y)-g(x)|^2 dx dy`.

The [literal cutoff limit](../3-formalized/pw-b-gamma-adjoint-cutoff-contact.md)
is now Lean-closed: all nine public declarations pass their axiom audits.
No full adjoint, closure, common form domain or complete pairing identity
is claimed yet. The admitted source-mode paired products and their
logarithmic contact are proved below; the complete transposition remains
necessary before asserting these operator conclusions.

## Concrete source tests and positive survivors

The actual normalized source modes are phi_1=1 and
phi_2=sqrt(2)*exp(-x). The Frullani identity gives A phi_1=0 and
A phi_2=-log(2)*phi_2; source fixation gives B phi_1=0.
The cross-pairing integral w*phi_2 is finite and strictly positive.
The [actual source test](../3-formalized/pw-b-gamma-adjoint-source-test.md)
now proves the corresponding exact defect for every positive integer n:
-log(n)*M_n, strictly negative for n>1. All inner responses and outer
paired integrals are admitted; every mode has finite weighted squared
norm. All28 public declarations pass the final scratch axiom audit.
This excludes the uncorrected pairing identity on these modes. Its
positive survivors are the finite strictly positive cross-mass and
exact all-mode defect; the corrected adjoint remains a candidate.
PW-B remains live.

For general positive integer n, w*phi_n is proportional to
exp(-n*x-1/x)/x. Inversion x ->1/(n*x), retaining its Jacobian, predicts
the exact logarithmic moment

`integral log(x)*w*phi_n=-(log(n)/2)*integral w*phi_n`.

The [logarithmic-moment theorem](../3-formalized/pw-b-gamma-adjoint-log-moment.md)
now proves the exact contact pairing for every positive integer n.
All11 public declarations pass the final scratch, including logarithmic
admission, the actual reciprocal derivative and integral substitution.
Their dependency-closed argument is explicit.
On x>0, the bounds log(x)<=x and -log(x)<=1/x give
|log(x)|<=x+1/x. Writing r=1/x, the elementary exponential-series
inequality r^2*exp(-r)<=2 yields

`|log(x)|*w(x)<=3*exp(-x)`.

Since 0<phi_n(x)<=sqrt(n), this is an admitted exponential majorant
for every positive integer mode's logarithmic cross-pairing. The map
j_n(x)=1/(n*x) is an involution of the positive ray with absolute
derivative 1/(n*x^2). Direct substitution gives

`|j_n'(x)|*w(j_n(x))*phi_n(j_n(x))=w(x)*phi_n(x)`

and log(j_n(x))=-log(n)-log(x). Thus the actual change-of-variables
formula, followed by linearity of admitted integrals, gives
J_n=-log(n)*M_n-J_n. Consequently the contact pairing 2*J_n equals
the complete ground-to-mode defect -log(n)*M_n. This is a positive
survivor of the uncorrected-adjoint obstruction, not a universal Ward
balance or an operator identity on the arithmetic domain.

The existing complete reflected-atom polynomial bound gives another
domain candidate: for each complex z, |R M_z/Q|<=1+C*x^m for suitable
C,m, hence |M_z/Q|<=1+C*x^(-m). The moments above would admit every
coefficient parameter in L2(w dx). Such admission would supply no Xi
selection. Preserve the complete series and prove the transformed
measure and bounds before claiming this domain result.

## Remaining full cutoff-pairing passage

The moment identity alone does not interchange the cutoff limit with
the whole source pairing. A direct paper estimate is available for
that additional step. On x>2*delta, the proved remainder bound and
|log(1-delta/x)|<=2*delta/x give

`|contact(x,delta)-2*log(x)|`
` <=delta*(1+2/x+2/x^2)`.

The cross-density has finite inverse moments, which still need their
explicit Lean admission proof. On delta<x<=2*delta, positivity and
exp(-h)<=1 bound the absolute contact by
|log(x)|+|log(x-delta)|. Since

`w(x)*phi_n(x)<=sqrt(n)*exp(-1/(2*delta))/delta`,

the integral over this layer is bounded by
sqrt(n)*exp(-1/(2*delta))*(1-2*log(delta)) for small positive delta,
which tends to zero. The original adjoint cutoff also retains a
separate loss term on0<x<=delta where its incoming interval is empty.
Its pairing is bounded by sqrt(n)*delta*(1-log(delta)), using the
actual admitted tail integral of exp(-h)/h. It cannot be silently
replaced by the contact expression outside its positive-cutoff range.
All three regions and the finite-cutoff transposition must be proved
before claiming convergence of the original adjoint pairing. These
are pending paper estimates, not new Lean results or a closed-domain
operator identity.

## Complete arithmetic endpoint and scalar source test

The [reciprocal-endpoint theorem](../3-formalized/pw-b-gamma-reciprocal-endpoint.md)
proves the actual derivative of q_a(v)=exp(-a/v) and the all-order bound

`0<=q_a'(v)<=(k+2)!/a^(k+1)*v^k`.

The mean-value theorem on [v,v+h] controls the complete kernel by
`((k+2)!/a^(k+1))*exp(-h)*(v+h)^k`, without the former1/v loss.
The actual positive endpoint kernel exp(-h-a/h)/h is integrable. The
original kernels converge to it in L1, and their integrals converge.
On0<v<=1, the shifted Gamma moment gives a common integral bound at
every inverse polynomial order in a. All14 public declarations, the
targeted leaf build, index and final lint are verified.

The [complete arithmetic endpoint](../3-formalized/pw-b-gamma-arithmetic-reciprocal-endpoint.md)
retains the entire signed Möbius series and identifies its limit with
the original normalized current H(R M_z)/Q as v->0+. For |z|<=N,
coefficient norms are at most n^(N+1); k=N+2 makes the complete tail
bounded by a constant times1/(n-1)^2. Tannery proves the finite endpoint
B_z for every complex z and absolute summability of its series. All11
public declarations and final integration audits are verified. No
endpoint parameter analyticity or relation to Xi is asserted.

The [skew-source theorem](../3-formalized/pw-b-gamma-skew-source-endpoint.md)
proves M_z/Q->1, E_z/Q->0, and the actual reflected-current quotient
R(H(R M_z))/Q->B_z at infinity. Hence the literal proposed skew source

`K_z=E_z-R(H(R M_z))-2*log(x)*M_z`

obeys K_z/(Q*log(x))->-2. It cannot equal any scalar multiple of the
unchanged M_z on the positive ray. The [failed raw-source ansatz](../5-failed/pw-b-raw-gamma-skew-occurrence.md)
is narrowly retired; PW-B, corrected fields and distributional source
realizations remain live. Its positive survivor is exact and stronger
than exclusion: adding2*c*log(x)*Q gives leading quotient2*c-2, so the
explicit scalar equation with M_z-c*Q forces c=1. At c=1 this quotient
vanishes for every z. All8 public declarations pass their standard-only
scratch audit, targeted leaf build, all-name source/API and exact
proof-body checks, index and final repository lint. These statements
do not prove a full-domain adjoint or existence of a corrected scalar
solution.

## Verified corrected-source boundary test

The unit ground subtraction survives the leading logarithmic test.
The next exact quantity to retain is B_z, the complete signed endpoint
above. The new Lean proof gives a further necessary condition. At x=1,
let d_n be the admitted normalized source atom and let C_z be the sum
of |d_n| over n>=2. The proved atom transport gives for x>=1

`|M_z(x)/Q(x)-1|<=C_z*exp(-(x-1))`.

The analogous logarithmic coefficient sum gives the same exponential
bound for E_z/Q. The elementary log(x)<=x bound and the already used
exponential-series estimate show log(x)*exp(-x)->0. Consequently the
unit-ground-corrected skew expression, divided by Q, tends to
-B_z. A scalar equation with M_z-Q therefore requires B_z=0.
The [unit-ground boundary theorem](../3-formalized/pw-b-gamma-ground-boundary.md)
proves this rate and boundary condition, plus the all-power decay of
the reflected current required by that scalar equation. These are not
an eigenfunction or an identification of B_z with Xi. The next attack
is the all-moment extraction below and actual source/spectral incidence.
Merely declaring B_z zero at a selected parameter would assume the
missing producer.

The four new deep searches and their source/compiler freshness limits
are preserved in the [endpoint search record](pw-b-gamma-reciprocal-flat-endpoint-searches.json).
The useful methods are the actual mean-value theorem, admitted Gamma
majorants, dominated integral convergence and Tannery. Proposed Sonin
L2 and strong-log Mellin carriers do not establish admission or spectral
occurrence for this source. The [attack journal](pw-b-source-orientation-attack.md)
records the recent broad arXiv papers and their missing transfer premises.

## Lean and research state

Scratch: `/tmp/pwb-gamma-reversible-pairing.lean`.
All18 public declarations now pass in the final scratch with only
propext, Classical.choice and Quot.sound. They include density uniqueness,
actual source-square weight, log-coordinate gain, integrability, the
reciprocal displacement derivative and the exact rate/Jacobian identity.
The [reversible-density theorem](../3-formalized/pw-b-gamma-reversible-density.md)
is promoted and wired into RHTower. Its targeted build, index, all18
public-name and axiom checks, and repository formal lint passed.
Next proof order:

1. Prove the full original cutoff-pairing passage, including its empty incoming region; the literal limit, source cross-test and admitted logarithmic contact pairing are proved.
2. Derive the complete admitted pairing identity and arithmetic domain.
3. Identify an actual Xi occurrence and source-forced Ward law; none of
   the preceding identities supplies that final step.

[Pairing search records](pw-b-gamma-reversible-pairing-searches.json) and
the reversible search in the [endpoint records](pw-b-gamma-endpoint-subtraction-searches.json)
retain partial coverage of723712 declarations, candidates and ingredient
sets. The proposed finite-fibre, cusp-eigenform and uniformly bounded-weight
arguments were checked and do not establish this singular source domain.
The [main attack card](pw-b-source-orientation-attack.md) records the
recent broad arXiv searches and the exact limitations of their transfer.


## Stronger corrected-source attack: all retained moments (conjecture)

The next conjecture is sharper than B_z=0. Write
F_z(y)=M_z(y)/Q(y)-1 and S_z(t)=F_z(1/t). The complete normalized
reciprocal current is
C_z(v)=integral_(h>0) exp(-h)(S_z(v+h)-S_z(v))/h dh.
A unit-corrected scalar identity would make C_z(v) smaller than every
power of v as v->0+. The equivalent statement after inversion v=1/x
is now proved in the unit-ground boundary theorem using the full signed
source and logarithmic-current tails. It is a necessary consequence of
the scalar identity; existence of that identity is not assumed.

Candidate expansion: exp(-v) C_z(v) has asymptotic coefficients
J_j(z)=integral_(t>0) exp(-t) S_z(t)/t^(j+1) dt for every j>=0.
To prove it, split the original h-integral at h=v. The region0<h<v
can use a derivative bound on S_z on[v,2v], or directly the already
verified modewise flat-kernel bound detailed below. It cannot be split
into separate divergent integrals. On h>=v, put t=v+h and expand1/(t-v)
finitely, where v/t<=1/2.
Bound its remainder by2*v^(N+1)*integral_(t>0) exp(-t)|S_z(t)|/t^(N+2).
The subtracted loss is bounded by |S_z(v)|*(1+|log v|); replacing the
remaining lower limit2v by0 requires separate flat-tail estimates.
None of these full-series, all-order estimates is yet formalized.

If that expansion is proved, flatness forces every J_j(z)=0 by induction.
Inversion t=1/y turns these into ordinary moments of
g_z(y)=exp(-1/y)*F_z(y)/y on y>0. A single exponential window suffices
for moment uniqueness: the actual corpus theorem
HTGeometry.ae_eq_zero_of_forall_complex_moment_eq_zero
in LocalExponentialTestClosure requires finite measure, an exponential
window and an L2 density. Candidate realization: measure exp(-y/2)dy
on y>0 and density exp(y/2)*g_z(y). Its hypotheses still need source
proofs, particularly at y=0. Absolute arithmetic admission gives the
mechanism for polynomial growth there, killed by exp(-1/y).

Zero density would force F_z=0. The complete n=2 leading-tail limit
should contradict this for every z, since its coefficient is nonzero.
This last all-z leading limit also needs proof; the older leading-current
leaf alone treats the untilted current and cannot be cited for it.
Thus the conjectured exclusion of the unit-corrected scalar ansatz is
NOT a proved no-go. Its positive survivor is the complete endpoint
moment detector: some retained J_j(z) must be nonzero. PW-B remains live.


### Quantitative proof candidate for the all-moment step

Let a_n=mu(n)*sqrt(n)*exp(-z*log n), n>=2. Fix integer N with
|a_n|<=n^N, available from the coefficient bounds. For0<t<=1,
(n-1)/t >= 1/(2t)+(n-1)/2. Therefore
|S_z(t)|<=A_N*exp(-1/(2t)),
|S_z'(t)|<=D_N*t^(-2)*exp(-1/(2t)),
where A_N=sum_(n>=2)n^N exp(-(n-1)/2) and
D_N=sum_(n>=2)n^N(n-1)exp(-(n-1)/2) are finite.
The same term bounds locally uniformly justify termwise differentiation
on each compact subinterval of t>0. For0<v<=1/2, the original near
integral0<h<v is then bounded by D_N*v^(-1)*exp(-1/(4v)).
This is smaller than every power of v. It retains the cancellation
inside the difference quotient throughout.

At t>=1, the elementary exponential-series inequality bounds
n^N exp(-n/t) <= N!*(2t)^N*exp(-n/(2t)). Summing the geometric tail
and using exp(u)-1>=u bounds S_z(t) by a constant times t^(N+1).
Hence every absolute J_j integral is finite: exponential suppression
at t=0 and at t=infinity dominates the respective powers. These
bounds also make the missing0<t<2v moment pieces flat at every fixed
order. The far-region finite geometric expansion above thus yields
exp(-v)C_z(v)=sum_(j=0)^m J_j(z)*v^j+O_z,m(v^(m+1)).
No bound uniform in m is being claimed or used.

The inversion density g_z consequently satisfies an exponential bound
at infinity and a polynomial times exp(-1/y) bound at zero. The
proposed finite measure and L2 density therefore satisfy the single
exponential-window uniqueness theorem. Finally, dominated convergence
with the admitted n>=2 coefficients at x=1 gives
exp(x-1)*F_z(x) -> a_2*exp(-1), which is nonzero for every z.
Thus not all J_j(z) can vanish. Choosing their first nonzero index j
would give C_z(v)/v^j -> J_j(z) != 0, contradicting the all-power
flatness forced by a corrected scalar equation.

This is the explicit proof candidate and positive survivor to audit:
every parameter has a finite first nonzero retained endpoint moment.
It does not imply any uniform bound on that first index, and it does
not identify the endpoint moments with Xi. The all-order source
bounds, expansion, density transport and all-z n=2 limit remain to be
checked in Lean before this candidate can retire the corrected ansatz.


### Lean-guided simplification of the near-region argument

The already verified reciprocal-kernel flat bound removes the need to
differentiate the complete source. For each mode a=n-1>0 it gives
|K_a(v,h)| <= ((k+2)!/a^(k+1))*exp(-h)*(v+h)^k.
Choose k larger than both the requested endpoint order and the fixed
coefficient growth degree. Then sum |a_n|/a^(k+1) absolutely. On0<h<v,
(v+h)^k <= (2v)^k, so the entire original near-region integral is
O_z,k(v^(k+1)). Arbitrarily high fixed k supply exactly the required
flatness while retaining the original cancellation. This can reuse
ThetaCuspHawkingParikhWilczekGammaReciprocalEndpoint directly.

The same elementary bound exp(-a/t)<=p!*t^p/a^p supplies two further
closures. Taking p larger than the coefficient growth degree proves
|S_z(t)|<=C_z,p*t^p for all t>0, hence |F_z(y)|<=C_z,p*y^(-p) near y=0.
Taking p larger than both that degree and j proves absolute admission
of the j-th moment by the majorant
p!/a^p * integral_(t>0) exp(-t)*t^(p-j-1)dt.
The Gamma integral is finite; the remaining coefficient sum converges.
At t=0 one can take p arbitrarily large to control each removed moment
piece. Thus the existing reciprocal flat-kernel theorem, exponential
tail theorem and ordinary Gamma admission offer a source-faithful
formalization path for every boundary remainder. These observations
are a concrete proof simplification, not a completed all-moment audit.


## Iteration28 verified source-tail and first boundary results

All10 declarations in the [unit-ground boundary theorem](../3-formalized/pw-b-gamma-ground-boundary.md)
pass scratch Lean with standard-only logical axioms. In particular,
the complete source/current exponential bounds and all polynomially
weighted tail limits are closed, as are the corrected boundary limit
-B_z and the all-power current flatness required by a scalar identity.
The exact proofs are promoted and wired. The targeted leaf build
passed in482s; index, all10 source/API names, exact scratch-body match
and repository formal lint passed. The all-moment expansion, moment
density realization and all-z first nonzero source coefficient remain
unformalized. The earlier candidate sections above describe those
remaining tasks, not an already completed corrected-source no-go.


## Closed high-order moment detector: normalization recovers n=2

The corpus BesselK1RayCoefficients identifies ray coefficients through
Schlaefli/Gamma integral representations. Applying that mechanism to
these actual endpoint moments gives a shorter positive survivor than
general moment determinacy. The [positive kernel bounds](../3-formalized/pw-b-gamma-reciprocal-moments.md)
and [complete signed source detector](../3-formalized/pw-b-gamma-moment-detector.md)
are now closed in Lean with both targeted leaf builds passed.

For a>0 and integer j>=2 define
I_j(a)=integral_(t>0) exp(-t-a/t)/t^(j+1)dt.
The substitution u=a/t gives
I_j(a)=a^(-j)*integral_(u>0) exp(-u-a/u)*u^(j-1)du.
The elementary inequalities1-a/u<=exp(-a/u)<=1, together with
Gamma(j)=(j-1)*Gamma(j-1), imply

`a^(-j)*(1-a/(j-1)) <= I_j(a)/Gamma(j) <= a^(-j)`.

The lower bound need not be positive; the actual integral is positive.
For a=1 it forces I_j(1)/Gamma(j)->1. For a>=2 the upper bound tends
to0. For fixed complex z, choose one integer j0 larger than the
coefficient growth degree plus2. For all j>=j0, the n>=3 terms satisfy

`|a_n*I_j(n-1)/Gamma(j)| <= |a_n|/(n-1)^j0`,

with a summable right side. Dominated convergence therefore gives

`J_j(z)/Gamma(j) -> a_2(z) = -sqrt(2)*exp(-z*log(2)) != 0`.

This retains the full signed coefficient series and uses a fixed
summable bound in j. It makes every sufficiently high endpoint moment
nonzero for each fixed z, stronger than existence of some nonzero
moment. No uniform starting moment in z is claimed. Combined with
the original integral's all-order endpoint expansion, it would exclude
the unit-ground-corrected scalar ansatz at every parameter.

The reciprocal integral substitution, normalized Gamma squeeze, complete
arithmetic high-order limit and exact original-source integral identity
are now proved. Next prove the original cutoff expansion and extract
its coefficients from the already verified all-power current flatness.
The local exponential-window argument remains an independent backup;
the preferred proof does not need that measure construction, an L2
realization, or the separate all-z n=2 source-tail theorem. These
results close the endpoint-moment detection step; cutoff extraction remains open. They do
not construct Xi occurrence or Ward balance, and PW-B remains live.


The verified Lean indexing is: use j=k+2 with
k:nat, so every Gamma recurrence and comparison integral is admitted
without a separate j>=2 premise. Use the existing
pwGammaMobiusReciprocalCoefficient z n and a=n+1; its n=0 term is
exactly the surviving n=2 arithmetic coefficient. The normalized
main-mode error is at most1/(k+1), and all n>=1 terms are dominated
by a fixed inverse power chosen from the coefficient growth bound.
The actual source integral is absolutely admitted at every natural k;
its normalized full signed series tends to the stated nonzero coefficient.


### Optional quantitative refinement; not yet formalized

Choose one integer p>=2 with
C_z,p=sum_(n>=3)|a_n|/(n-1)^p finite. For every integer j>=p,
(n-1)^(-j) <= (n-1)^(-p)*2^(p-j) on n>=3. The complete signed
moment error therefore satisfies

`|J_j(z)/Gamma(j)-a_2(z)| <= |a_2(z)|/(j-1)+C_z,p*2^(p-j)`.

This replaces the last dominated-convergence step with an explicit
complete-tail bound. Put j=p+k to avoid subtraction in natural powers.
The right side tends to0 and eventually falls below |a_2(z)|, proving
eventual moment nonvanishing with an explicit error bound. Qualitative
eventual nonvanishing is already proved by a fixed summable bound and
dominated convergence. This optional rate refinement is not needed for
the next cutoff extraction; it still makes no uniform claim
about p or the starting index across all complex z.


### The asymptotic expansion cannot be replaced by a convergent series

The [exact moment-series divergence](../5-failed/pw-b-convergent-endpoint-moment-series.md)
now proves in Lean that J_k(z)*w^k does not tend to zero for
any nonzero w, at every complex source parameter. The normalized
nonzero Gamma limit is its positive survivor. The current has not yet
been identified with any endpoint series; no assertion about its
analyticity follows yet. This rules out using an assumed analytic
power-series expansion as the missing coefficient-extraction proof.
Next retain the original h<v piece, shift the h>=v piece, and estimate
the finite geometric remainder and all removed endpoint terms.
