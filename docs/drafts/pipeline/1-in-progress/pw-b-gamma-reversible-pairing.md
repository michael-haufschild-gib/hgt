# PW-B pairing forced by the two actual jump directions

- **ID:** PW-B-GAMMA-REVERSIBLE-PAIRING-2026-09-11
- **Stage:** 1-in-progress
- **Status:** Reversible density, uniqueness, source weight, Jacobian, literal cutoff contact, actual source-mode defect and its exact logarithmic pairing are Lean-closed. Full adjoint, source domain and spectral occurrence remain open.
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

## Next corrected-source boundary test

The unit ground subtraction survives the leading logarithmic test.
The next exact quantity to retain is B_z, the complete signed endpoint
above. A paper derivation gives a further necessary condition. At x=1,
let d_n be the admitted normalized source atom and let C_z be the sum
of |d_n| over n>=2. The proved atom transport gives for x>=1

`|M_z(x)/Q(x)-1|<=C_z*exp(-(x-1))`.

The analogous logarithmic coefficient sum gives the same exponential
bound for E_z/Q. The elementary log(x)<=x bound and the already used
exponential-series estimate show log(x)*exp(-x)->0. Consequently the
unit-ground-corrected skew expression, divided by Q, should tend to
-B_z. A scalar equation with M_z-Q would therefore require B_z=0.
This sharper rate and boundary condition are pending Lean work, not a
claimed eigenfunction or an identification of B_z with Xi. The next
attack must prove the complete rate and retained boundary functional,
then establish their actual source/spectral incidence. Merely declaring
B_z zero at a selected parameter would assume the missing producer.

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
power of v as v->0+. This flatness must be proved using the full signed
source and logarithmic-current tails. It is not assumed.

Candidate expansion: exp(-v) C_z(v) has asymptotic coefficients
J_j(z)=integral_(t>0) exp(-t) S_z(t)/t^(j+1) dt for every j>=0.
To prove it, split the original h-integral at h=v. The region0<h<v
requires a derivative bound on S_z on[v,2v], not separate divergent
integrals. On h>=v, put t=v+h and expand1/(t-v) finitely, where v/t<=1/2.
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
