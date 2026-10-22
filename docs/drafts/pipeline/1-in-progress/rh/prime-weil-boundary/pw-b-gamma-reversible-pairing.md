# PW-B pairing forced by the two actual jump directions

- **ID:** PW-B-GAMMA-REVERSIBLE-PAIRING-2026-09-11
- **Stage:** 1-in-progress
- **Status:** Reversible density, uniqueness, source weight, Jacobian, literal cutoff contact, actual source-mode defect and its exact logarithmic pairing are Lean-closed. Complete high-order source moments, finite original-current cutoff extraction and the nonzero finite endpoint order are Lean-closed. The specific unit-ground-corrected Gamma scalar equation is excluded at every parameter. The complete two-parameter paired contact, moving-layer passage and empty incoming constant loss are Lean-closed. Complete forward response, original gain transposition and the full paired original-current adjoint are Lean-closed. Physical common-domain adjoints, actual Xi occurrence and independent Ward balance remain open.
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

The [literal cutoff limit](../../../3-formalized/pw-b-gamma-adjoint-cutoff-contact.md)
is now Lean-closed: all nine public declarations pass their axiom audits.
The subsequent [full original-current paired identity](../../../3-formalized/pw-b-gamma-full-paired-adjoint.md)
now closes complete transposition with the retained contact. Closure, a
physical common form domain and operator-adjoint equality remain unproved.
The admitted source-mode tests below explain why the contact is necessary.

## Concrete source tests and positive survivors

The actual normalized source modes are phi_1=1 and
phi_2=sqrt(2)*exp(-x). The Frullani identity gives A phi_1=0 and
A phi_2=-log(2)*phi_2; source fixation gives B phi_1=0.
The cross-pairing integral w*phi_2 is finite and strictly positive.
The [actual source test](../../../3-formalized/pw-b-gamma-adjoint-source-test.md)
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

The [logarithmic-moment theorem](../../../3-formalized/pw-b-gamma-adjoint-log-moment.md)
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

## Complete paired contact and remaining transposition

The [complete signed paired-contact theorem](../../../3-formalized/pw-b-gamma-adjoint-paired-contact.md)
now proves the full contact integral limit for every two complex source
parameters. It retains the entire moving layer by translating x=u+delta to
the fixed positive u ray. The complete paired density is bounded by
C*x*exp(-x), giving an integrable logarithmic majorant independent of delta.
The empty incoming constant loss remains separate and has norm at most
C*delta. Every original integral in this passage is absolutely admitted.
Fourteen public theorems passed final scratch and the26-second targeted build.

The subsequent complete response and gain proofs now supply the changing-source
limit, omitted initial response, full transposition and reciprocal substitution.
The final section records their assembly into the paired original-current
identity. A full physical operator adjoint and its domain remain unproved.

## Complete arithmetic endpoint and scalar source test

The [reciprocal-endpoint theorem](../../../3-formalized/pw-b-gamma-reciprocal-endpoint.md)
proves the actual derivative of q_a(v)=exp(-a/v) and the all-order bound

`0<=q_a'(v)<=(k+2)!/a^(k+1)*v^k`.

The mean-value theorem on [v,v+h] controls the complete kernel by
`((k+2)!/a^(k+1))*exp(-h)*(v+h)^k`, without the former1/v loss.
The actual positive endpoint kernel exp(-h-a/h)/h is integrable. The
original kernels converge to it in L1, and their integrals converge.
On0<v<=1, the shifted Gamma moment gives a common integral bound at
every inverse polynomial order in a. All14 public declarations, the
targeted leaf build, index and final lint are verified.

The [complete arithmetic endpoint](../../../3-formalized/pw-b-gamma-arithmetic-reciprocal-endpoint.md)
retains the entire signed Möbius series and identifies its limit with
the original normalized current H(R M_z)/Q as v->0+. For |z|<=N,
coefficient norms are at most n^(N+1); k=N+2 makes the complete tail
bounded by a constant times1/(n-1)^2. Tannery proves the finite endpoint
B_z for every complex z and absolute summability of its series. All11
public declarations and final integration audits are verified. No
endpoint parameter analyticity or relation to Xi is asserted.

The [skew-source theorem](../../../3-formalized/pw-b-gamma-skew-source-endpoint.md)
proves M_z/Q->1, E_z/Q->0, and the actual reflected-current quotient
R(H(R M_z))/Q->B_z at infinity. Hence the literal proposed skew source

`K_z=E_z-R(H(R M_z))-2*log(x)*M_z`

obeys K_z/(Q*log(x))->-2. It cannot equal any scalar multiple of the
unchanged M_z on the positive ray. The [failed raw-source ansatz](../../../5-failed/pw-b-raw-gamma-skew-occurrence.md)
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
The [unit-ground boundary theorem](../../../3-formalized/pw-b-gamma-ground-boundary.md)
proves this rate and boundary condition, plus the all-power decay of
the reflected current required by that scalar equation. These are not
an eigenfunction or an identification of B_z with Xi. The finite extraction below now excludes this scalar equation. The next
attack is the full cutoff-pairing passage and actual source/spectral incidence.
Merely declaring B_z zero at a selected parameter would assume the
missing producer.

The four new deep searches and their source/compiler freshness limits
are preserved in the [endpoint search record](../../pw-b-gamma-reciprocal-flat-endpoint-searches.json).
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
The [reversible-density theorem](../../../3-formalized/pw-b-gamma-reversible-density.md)
is promoted and wired into RHTower. Its targeted build, index, all18
public-name and axiom checks, and repository formal lint passed.
Next proof order:

1. Derive the physical common operator domain and closure from the now proved complete source pairing identity.
2. Identify an actual Xi occurrence using a different justified field or realization.
3. Force fixed-grade Ward balance independently; neither the paired identity nor domain admission supplies this law.

[Pairing search records](../../pw-b-gamma-reversible-pairing-searches.json) and
the reversible search in the [endpoint records](../../pw-b-gamma-endpoint-subtraction-searches.json)
retain partial coverage of723712 declarations, candidates and ingredient
sets. The proposed finite-fibre, cusp-eigenform and uniformly bounded-weight
arguments were checked and do not establish this singular source domain.
The [main attack card](pw-b-source-orientation-attack.md) records the
recent broad arXiv searches and the exact limitations of their transfer.


## Closed finite cutoff extraction and corrected scalar obstruction

The [complete source bounds](../../../3-formalized/pw-b-gamma-reciprocal-cutoff-source.md)
prove S_z(t)=M_z(1/t)/Q(1/t)-1 is flat to every order at t=0 and has polynomial
growth at infinity. All original coefficients

`B_j(z)=integral_(t>0) exp(-t)*S_z(t)/t^(j+1) dt`

are absolutely admitted, including j=0,1. For the complete original current
C_z(v)=integral_(h>0) exp(-h)*(S_z(v+h)-S_z(v))/h dh,
[finite cutoff extraction](../../../3-formalized/pw-b-gamma-reciprocal-cutoff-expansion.md)
now proves, for every q and all0<v<=1/2,

`norm(exp(-v)*C_z(v)-sum_(j<q)v^j*B_j(z))<=C_z,q*v^q`.

The proof splits at h=v before separating gain and loss. It retains the near
response and every removed0<t<2v moment piece. The translated far integral
has an exact finite geometric remainder, bounded by2*v^q times the complete
admitted norm moment. The loss uses1/h<=1/v on h>v and source flatness.
There is no convergent-series premise and no bound uniform in q.

The [complete signed detector](../../../3-formalized/pw-b-gamma-moment-detector.md)
proves B_(k+2)/(k+1)! tends to the nonzero actual coefficient
-sqrt(2)*exp(-z*log2). Every sufficiently high B_(k+2) is therefore nonzero.
Select the least nonzero B_j. Multiplying the finite remainder at order j+1
by x^j after v=1/x proves

`x^j*exp(-1/x)*C_z(1/x) -> B_j(z) != 0`.

This [finite-order survivor and exact no-go](../../../5-failed/pw-b-corrected-gamma-scalar-occurrence.md)
is now Lean-closed. The corrected scalar equation would force the same
quantity to tend to zero at every order, contradicting this limit. Only that
specific unchanged Gamma/Mobius pointwise scalar ansatz is retired. PW-B,
other source fields and properly derived weak realizations remain live.
No uniform first index or equality of the moments with Xi is asserted.

The alternative exponential-window moment-determinacy construction is no
longer needed for this proof. Its measure/L2 admission and a separate all-z
n=2 tail theorem are not claimed as formalized. The actual Gamma-normalized
complete detector supplies the needed nonzero coefficient directly.

## Remaining mathematical attack

The finite-cutoff transposition and complete paired limit, including the moving
layer and empty incoming interval, are now proved. Derive a justified physical
common operator domain and closure. The corrected scalar obstruction means
actual Xi occurrence must use another justified field or realization. Neither
the paired identity nor all-parameter admission forces Ward balance.

## Divergent series and optional rate refinement

The [moment-series obstruction](../../../5-failed/pw-b-convergent-endpoint-moment-series.md)
proves J_k(z)*w^k fails to tend to zero for every nonzero w. The finite expansion
above is now proved, so its coefficients are identified with the original
current; no separate Lean analyticity/nonanalyticity theorem is asserted.

An optional quantitative detector bound remains unformalized. With
C_z,p=sum_(n>=3)|a_n|/(n-1)^p finite and j>=p>=2,

`|B_j(z)/Gamma(j)-a_2(z)| <= |a_2(z)|/(j-1)+C_z,p*2^(p-j)`.

The qualitative complete detector already suffices. This refinement is not
needed for the corrected-scalar no-go and would make no uniform claim in z.
The [attack journal](pw-b-source-orientation-attack.md#iteration30-original-cutoff-coefficient-extraction)
retains the conjecture/proof/pivot history, research coverage and build evidence.

## Iteration31 verified mechanism: translate the moving contact layer

The complete contact passage is now proved without deleting a region. For a
complete paired density P, change x=u+delta in its contact integral over
x>delta. The entire moving layer is then part of the fixed positive u ray.
For0<delta<=1, positivity of the exponential contact kernel gives

`|contact(u+delta,delta)|<=|log(u+delta)|+|log(u)|`
`<=2*|log(u)|+u+1`.

If the actual P satisfies `|P(x)|<=C*x*exp(-x)`, this is dominated by
`C*(u+1)*exp(-u)*(2*|log(u)|+u+1)`, integrable on u>0. Continuity of P and
the two-variable contact limit yield the desired paired2log limit through
dominated convergence. The separate empty incoming term remains explicit:
its norm is at most `(exp(-delta)/delta)*integral_(0<x<delta)|P(x)|dx`,
hence at most `C*delta` using the same bound. This avoids a separate singular
layer estimate and a separate logarithmic loss asymptotic.

For the unchanged complete source pair
`P_z,v=w*conj(M_z/Q)*(M_v/Q)`, the proved reciprocal polynomial bound
gives `|M_z/Q|<=1+C_z*x^(-p_z)`. Each resulting inverse monomial
against exp(-1/x) is bounded by a factorial times x^2, giving the claimed
`C*x*exp(-x)` bound. The actual coordinate derivative proves continuity.
The complete signed source is retained. These paper steps and their exact Lean proofs are closed, with the targeted
leaf build passed. The subsequent full transposition is proved below; this
contact result alone does not assert an operator adjoint.

## Remaining transposition terms after the paired contact

The complete signed response passage is now closed in the
[paired-response proof](../../../3-formalized/pw-b-gamma-adjoint-paired-response.md).
All nineteen public theorems passed the final scratch without diagnostics;
the targeted leaf build passed in125s, and repository formal lint passed. With g_z=M_z/Q, retain

`H_z(v,h)=exp(-h)*(S_z(v+h)-S_z(v))/h`,

`a_delta(x)=delta/[x*(x-delta)]` for x>delta.

The complete kernel `J_z,v(x,h)=w(x)*g_v(x)*conj(H_z(1/x,h))` has the
proved joint majorant `C*x*exp(-x)*exp(-h)*(1+h)^r`. Both positive-ray
factors are integrable. Every positive-x section is also admitted.

The changing-field mismatch

`E_delta(x)=integral_(a_delta(x)..delta) H_z(1/x,h) dh`

vanishes after the original complete source pairing. The proof retains the
entire moving layer: the two product masks x>delta,h>a_delta(x) and
x>delta,h>delta are dominated by the same full kernel and converge to it.
Exact Fubini and difference-of-tail identities recover the original oriented
interval integral. Both native cutoffs pass simultaneously, including the
initially omitted0<x<=delta response region. Outer cutoff, mismatch and
limiting integrals are all admitted. The separate empty incoming constant
loss remains in the previous complete contact theorem.

The [complete gain proof](../../../3-formalized/pw-b-gamma-adjoint-gain-transposition.md)
now proves `(g_z)'=g_z-g_(z-1)` and its global inverse-polynomial derivative
bound. Mean-value control admits the entire forward paired response. The
original gain is transposed by a measure-preserving additive shear, admitted
Fubini and the actual injective reciprocal Jacobian. All original sections
and both outer integrals are separately admitted.

The [full paired adjoint](../../../3-formalized/pw-b-gamma-full-paired-adjoint.md)
proves the exact finite identity F_delta=R_delta+E_delta+(C_delta-L_delta).
Its limit is `integral w*conj(g_z)*A g_v = integral w*g_v*conj(B g_z)
+ integral w*conj(g_z)*g_v*2log(x)`, with both A and B identified as the
original arithmetic currents and every integral admitted. The gain leaf's
33 public theorems and this leaf's four public theorems passed scratch and
targeted builds in46s and124s respectively.

Physical common-domain adjoints, necessity of the pairing, a different
justified Xi occurrence and independent Ward balance remain open.

## Mellin evaluation is a separate domain test

The [exact dual-domain proof](../../../3-formalized/pw-b-gamma-mellin-dual-domain.md)
now verifies that w*|g_z|^2 is integrable for every complex source parameter.
The literal Mellin kernel k_s=x^(s-1)Q nevertheless has squared dual density
|k_s|^2/w=x^(2 Re s)*exp(-x+1/x), nonintegrable near zero for every s.
It is admitted on each compact interval away from zero. Hence the direct
global weighted Cauchy–Schwarz constant cannot supply the reader needed for
Xi incidence. Source-specific endpoint control, a stronger domain or a
justified weak reader remains required. A universal unbounded-extension
statement would require an additional duality or normalized-test proof.
