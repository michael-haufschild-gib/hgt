# Many-node certificates beyond every fixed one-node width

Status, 8 October 2026: MC2 below has a dependency-closed paper proof.
Lean implementation remains OPEN. Full PBAP and broad fixed-width MH2 remain
OPEN. This is a new application of classical derivative estimates, with
scientific novelty unestablished; the derivative test itself is not a result
of this cycle. No computations or numerical evidence are used.

## Exact statement and frontier

Let phi be the literal `jointUnitBumpTest`, m0=integral phi^2>0,
B=integral phi>0. Fix ANY kappa>0. At each sufficiently large prime p put

    L=log(p)/2, N=exp L, W=kappa L exp(-L/2),
    beta(u)=phi(u/W), m=W m0, rho(y)=Re autocorr(phi)(y).

Let e(T) be `jointPairFullEnergy beta L T`, with both poles retained. Define
the finite sums over integers n>=2 (terms outside the displayed support vanish)

    Z=sum_n rho((log n-L)/W)/n,
    F(T)=Z^(-1) sum_n rho((log n-L)/W) cos(T(log n-L))/n,
    c=4(cosh(L/2)-1) W^2 B^2.

**MC2:** eventually Z>0 and, for EVERY real T,

    e(T)+c F(T) >= m L/2.                                  (1)

Consequently every finite nonnegative exact real integer-null correction
has full energy at least L/4 times its literal physical mass. There is NO
upper bound on correction mass. The sector is nonempty at every prescribed
M>1 by the existing actual simultaneous correction construction.
For kappa>m0/(2B^2) its seed remains strictly negative.

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? The sharp one-node boundary should
be a limitation of that certificate, not a boundary of null-mixture
positivity. Formula (1) makes that assertion falsifiable: one actual prime
family, explicit coefficients at every active integer, and a uniform margin.
For kappa=3m0/B^2, the known lag bounds and seed/high-frequency estimates
rule out every nearest-node coefficient eventually, while (1) still applies.
Thus this mechanism crosses the preceding boundary rather than refining it.

Parent theories: Fourier autocorrelation positivity; cellwise FTC quadrature;
Abel summation; finite-order van der Corput. The first formerly [OPEN CORE]
was uniform cancellation on the actual shrinking interval, with its length
retained. The corpus's `phase_prefix_bound` supplies exactly that dependence.

## 1. A continuous pole certificate

Put Q(T)=integral rho(y) cos(Ty) dy and R(T)=Q(WT)/B^2.
The actual source is real, so Fourier autocorrelation gives Q(T)=|FT(phi)(T)|^2.
Therefore 0<=R<=1, R(0)=1. (The averaged +/- Fourier-square identity would
also suffice.) The dilated autocorrelation is W rho(y/W).

The already formalized full modulation identity has kernel

    K_L(y)=4 J(2y)-2[J(2(L+y))+J(2(L-y))]
             +8(cosh(L/2)-1) cosh(y/2),

where J is positive and strictly decreasing on positive arguments.
For 0<y<=W and 2W<L, the first bracket is nonnegative and cosh(y/2)>=1.
Nonnegativity of rho and 1-cos gives, without dropping either pole,

    e(T)-e(0)
      >=8(cosh(L/2)-1) integral_(0,infinity)
             W rho(y/W)(1-cos(Ty)) dy
      =c(1-R(T)).                                         (2)

All integrals exist: the source is smooth compact, the defect is O(y^2)
at zero, and the exact jump identity already pays its singular integrability.
Evenness and the substitution y=Wv pay the last equality. No monotonicity
of the full energy as a function of |T| is being asserted.

The existing uniform seed expansion, applied to the actual source, gives

    |e(0)+2m log W+c|
      <= W jointSeedLogCost(phi)+(cosh(L/2)-1)W^4 B^2.

The last term divided by m is O_kappa(L^3 exp(-L)), hence tends to zero.
Since -2log W=L-2log L-2log kappa, (2) proves uniformly in T

    e(T)+cR(T) >= m[L-2log L-O_kappa(1)].                   (3)

Also c/(mL)->a_kappa:=2kappa B^2/m0. This exact coefficient matters in the
large-frequency band. The continuous certificate alone does not cancel
integer-null constraints; discretization below is essential.

## 2. Low heights: actual integer quadrature

Apply cellwise FTC to the smooth compactly supported function

    g_T(x)=rho((log x-L)/W) exp(iT(log x-L))/x

on x>0, extended by zero. Its support is [N exp(-W),N exp W], eventually
above 2. Summing each cell's integral derivative bound yields

    |sum_n g_T(n)-integral g_T(x) dx|
      <= exp(W)/N [||rho'||_1+(1+|T|) W ||rho||_1].          (4)

Substitution y=(log x-L)/W makes the integral W Q(WT), real for this
source. At T=0, Z/(WB^2)->1. In particular Z>0 eventually. Dividing (4)
and correcting the normalizer, using |R|<=1, proves

    |F(T)-R(T)| <= C_phi[1/(NW)+(1+|T|)/N]                 (5)

eventually, uniformly in T. For |T|<=N/sqrt L, this tends to zero and is
O_kappa(L^(-1/2)). Nonnegative node weights give |F(T)|<=1 at ALL heights.

## 3. Intermediate heights: keep the short length

For every FIXED a>1,

    sup_(N/sqrt L<=|T|<=N^a) |F(T)| -> 0.                 (6)

Here are all transition ranges; no long-block estimate is divided by a
shrinking width. Let n0=ceil(N exp(-W)), n1=floor(N exp W)+1 and H=n1-n0.
Then n0/N->1, H/(NW)->2, and eventually n1<=2n0+1, H>=1.
Choose a fixed integer K>a. Split positive T into the adjacent bands

    N^(k-1)/sqrt L <= T <= N^k/sqrt L,  k=2,...,K.

They cover the whole range in (6) eventually. Negative T is conjugation.
The corpus `RHTower.Sieve.phase_prefix_bound` applies with

    lambda=T (k-1)!/[2pi(2n0)^k], D=2^k.

It bounds every pure-phase prefix by

    256 [H(4^k lambda)^(1/(D-2))
              +H^(1-4/D) lambda^(-2/D)].

For fixed k, the upper band endpoint gives lambda<=C_k L^(-1/2)<1;
the lower endpoint and H~2kappa L sqrt N give
H^2 lambda>=c_(k,kappa) L^(3/2). After dividing the prefix bound by H,
both terms tend to zero, uniformly on the WHOLE band:

    O_(k,kappa)(L^(-1/(2(D-2)))+L^(-3/D)).                  (7)

The nonnegative weight b(x)=rho((log x-L)/W)/x has supremum plus total
variation O_phi(1/N): differentiation and y-substitution give exactly a
bound by exp(W)/N times ||rho'||_1+W||rho||_1, plus its supremum.
Abel summation therefore bounds the weighted sum by O_phi(P/N), where P
is the uniform prefix bound. Since Z~WB^2 and H~2NW, (7) proves (6).
Only finitely many fixed derivative orders occur. No growing-order estimate
or exchange of asymptotic quantifiers has been used.

## 4. All-frequency certificate and literal null transfer

Choose fixed a>1 so that 2a>a_kappa+2. All constants and thresholds may
depend on kappa and this a; none depend on T or correction mass.

For |T|<=N/sqrt L, (3), (5), and c=O_kappa(mL) give

    e(T)+cF(T)>=m[L-2log L-O_kappa(sqrt L)]>=mL/2.

For N/sqrt L<=|T|<=N^a, the existing exact-mass uniform high-frequency
bound applies: N/sqrt L>=exp(7L/8) eventually and W=kappa L exp(-L/2).
It gives e(T)/m>=2log|T|-C_phi. Equation (6) then yields

    (e(T)+cF(T))/m>=2L-log L-C_phi-O_kappa(L)o(1)>=L/2.

For |T|>=N^a, use the same high-frequency estimate and F>=-1:

    (e(T)+cF(T))/m >=2aL-C_phi-c/m>=L/2.

This proves (1). Every contributing n satisfies 2<=n<p eventually; its
autocorrelation is active exactly when rho((log n-L)/W)!=0. Multiply each
literal active-node equation by rho((log n-L)/W)/(nZ) and sum to obtain

    F(0)+sum_i w_i F(t_i)=1+sum_i w_i F(t_i)=0.

Thus summing (1), including the seed at T=0, cancels the certificate exactly.
The energy is at least mL(1+M)/2; actual physical mass is 2m(1+M), proving
the asserted L/4 margin without a mass cap. All tests, signs, active nodes,
nonemptiness and poles are those of the existing literal construction.

## Hostile audit and next conjecture

MC1, the intermediate fixed-mass cost claim C/L->infinity, follows from
(5)--(6) by the earlier high-frequency-mass argument. MC2 is stronger for
energy: direct pole cancellation removes the mass cap. Do not formalize a
conditional MH2 wrapper or confuse fixed kappa with broad fixed W.

Possible failure points audited: exact factor 4 in c; width in the density;
the H^2 lambda term of the corpus's weaker derivative test; all adjacent
frequency bands; the 1/W normalization of quadrature; signed poles;
inactive nodes; unbounded correction mass. Each is paid above.
The current verdict is **PAPER PROVED, LEAN OPEN**. Scientific novelty and
significance beyond this particular family remain unestablished.

Primary parent: Arias de Reyna,
[Explicit van der Corput's d-th derivative estimate](https://arxiv.org/pdf/2407.02094).
The paper's general estimate is stronger than the version actually needed
here. The proof above uses the already present corpus statement verbatim.
The reflection-positive Hankel representation framework of
[Adamo--Neeb--Schober](https://arxiv.org/abs/2105.08522) assumes a positive
Hankel operator; it is not a producer for PBAP or a substitute for (4)--(7).

## MC3: growing-width survivor, with a uniform-order audit

The next bolder conjecture is the same explicit certificate at

    W=(m0/B^2) b L log log L exp(-L/2),  0<b<1/log 2.        (8)

This is a genuine increase of scale beyond every fixed one-node width.
It does NOT follow by substituting a variable kappa in MC2. The following
separate uniform-order argument closes its paper proof; Lean remains OPEN.

Write r=B^2/m0, kappa=(b/r)log log L, a=r*kappa+1, and take the integer
K=ceil(a)+1. Then K<=r*kappa+3 and D_k=2^k<=8(log L)^eta for every k<=K,
where eta=b log 2<1. Eventually N/2<=n0<=2N and H>=NW, while W tends
to zero. On the SAME bands as before,

    4^k lambda <= 4^K K^K/(2pi sqrt L) <= L^(-1/4).

The last inequality follows from K log(4K)=O(log log L log log log L)
=o(log L); no k-dependent constant is being hidden. At the lower endpoint,

    H^2 lambda >= kappa^2 L^(3/2)/(2pi 4^K) >= L

eventually, using (k-1)!>=1 and 4^K<=64(log L)^(2eta). Thus the normalized
prefix bound is at most

    512 exp(-(log L)^(1-eta)/32),                           (9)

uniformly over ALL derivative orders used. The constants in Abel summation
and Z/(WB^2)->1 depend only on phi, and H/(NW)->2 still holds. Consequently
the intermediate F error times kappa tends to zero. All derivative-test
hypotheses, including lambda<=1 and the entire interval span, are paid.

For low heights the quadrature error is O(1/sqrt L), so its energy cost is
O(m sqrt L log log L)=o(mL). The seed remainder divided by m is
O(kappa^3 L^3 exp(-L))=o(1). Hence (3) still gives m[L-o(L)].
For intermediate and high heights, use the ALREADY uniform high-frequency
bound with a fixed lower-width parameter, since eventually kappa>=m0/B^2
and W<=1. No constant depending on growing kappa enters that estimate.

Finally c/m=2r*kappa*L*(1-exp(-L/2))^2<=2r*kappa*L EXACTLY. Therefore for
|T|>=N^a, e(T)/m-c/m>=2L-O(1). The K bands cover through N^a since K>a
and N^(K-a)>=N eventually (K-a>=1). Equation (9) pays the middle range;
the low range was paid above. This proves (1) and its unrestricted-mass
null consequence at (8), with the same L/4 margin. The seed is eventually
negative, by the explicit seed expansion, since r*kappa=b log log L->infinity.

Hostile verdict for MC3: **PAPER PROVED, LEAN OPEN**, scientific novelty
unestablished. The numerical constant 1/log 2 is a limit of this particular
derivative schedule, not a proved sharp positivity boundary. Do not claim
failure at or above that constant. The full broad-profile scale W fixed
and the arbitrary-profile null cone remain unresolved.

Implementation order stays dependency-driven: continuous certificate,
quantitative short-prefix estimate, actual quadrature/Abel transfer, then
uniform frequency-band schedule and actual-prime capstone. The quantitative
lemmas should retain enough parameters to support MC3 without duplicating
the MC2 construction. Next attack whether a sharper corpus derivative test
or a different separator extends this scale again; full PBAP stays active.

## Current search and process audit

Inspected all returned candidate and source-argument statements and ingredient
sets in `/tmp/wp01-mh2-frontier-refresh-20261008b.json` (partial=false),
`wp01-multiplicative-hankel-audit-20261008.json` (partial=true, coverage pending),
`wp01-hankel-cost-exact-20261008.json` (partial=false, 68,780 files),
`wp01-short-window-phase-20261008.json` (partial=true, 68,780 files), and
`wp01-many-node-certificate-exact-20261008.json` (partial=false, 68,781 files).
Most compiler metadata remains pending; applicability was checked in source,
not inferred from retrieval rank. Proposed ingredient chains about phase
shifts, positive-completion receivers and shifted defects do not supply this
certificate. `phase_prefix_bound` was inspected directly, including its H
dependence. Search misses do not establish absence or novelty.

Serena symbol lookup returned `path is ignored` for the owned Lean files;
source reads and patch edits are the fallback. One accidental overlap of
the API probe and first source check was caught; the API process exited,
its owned PID was verified absent, and subsequent Lean checks are serial.

## MC4: fixed complex profiles and signed certificate coefficients

The proof investigation exposes a stronger survivor. Positivity of rho is
needed by the convenient jump-kernel proof in section 1, but is NOT needed
by the underlying certificate. This section gives a separate paper proof;
it must not be inferred from the nonnegative-correlation Lean leaf.

Fix any nonzero complex smooth phi supported in [0,1]. Put

    m0=integral |phi|^2>0, A=integral |phi|,
    rho(y)=Re autocorr(phi)(y), J=integral |rho(y)|>0,
    Q(T)=integral rho(y) cos(Ty) dy.

The positivity J>0 follows from continuity and rho(0)=m0. Modulated
autocorrelations give Q(T)>=0 even for a complex source; explicitly it is
the average of |FT(phi)(T)|^2 and |FT(phi)(-T)|^2. Q(0)=|integral phi|^2
may be zero. No division by that quantity will be used.

For 0<b<1/log 2, let

    kappa(L)=(m0/J) b log log L, W=kappa(L)L exp(-L/2),
    G(T)=W^(-1) sum_(n>=2) rho((log n-L)/W) cos(T(log n-L))/n,
    D(T)=4(cosh(L/2)-1)W^2 G(T).

**MC4:** eventually e(T)+D(T)>=mL/2 for all real T, and therefore every
actual real integer-null correction has full energy >=L/4 times physical
mass. The certificate coefficients can have either sign. Correction
weights remain nonnegative. There is no mass cap and the existing full
phase construction makes the class nonempty at every M>1.

### Uniform Gamma floor without a sign condition on rho

The exact paired Fourier density d_T is nonnegative, has integral 4pi m
when W<L, and satisfies d_T(xi)<=4W^2 A^2 uniformly in L,T,xi. The latter
uses the actual interference factor <=4 and the L1 bound on each Fourier
translate. The known symbol lower bound is

    gamma(xi)>=log(2+|xi|)-C0, C0=10+log 4.

For xi!=0 it implies

    gamma(xi)>=-log W-C0-h(W xi),
    h(v)=1_(0<|v|<1) |log|v||.

Here h>=0 and integral h=2. The singleton xi=0 is null. Integrating against
d_T/(2pi), using its EXACT mass for the constant part and its pointwise
bound only for h, gives

    Gamma(pair,T)>=-2m log W-2m C0-4W A^2/pi.              (10)

All integrability is paid by the existing Gamma integrability and compact
log-singularity integrability; no uniform spectral-moment assumption is
introduced. This is an elementary uncertainty estimate, not a novelty claim.

### Uniform two-pole correction for signed rho

The actual cluster factor and paired autocorrelation give exactly

    Pole(pair,T)=-4(cosh(L/2)-1)W^2
                   integral cosh(Wy/2) rho(y) cos(WTy) dy.

For W<=1, support |y|<=1 and the existing cosh remainder imply

    |Pole(pair,T)+4(cosh(L/2)-1)W^2 Q(WT)|
       <=(cosh(L/2)-1)W^4 J.                             (11)

This bound is uniform in T and uses |rho|, so it does not silently assume
the missing sign condition. Equations (10)--(11) prove the needed
continuous certificate with remainder O_phi(W)+O(CW^4 J).

### Signed quadrature and the three frequency ranges

The FTC and Abel estimates above hold with |rho| and |rho'|. Thus G(T)
approximates Q(WT) with error O_phi(1/(NW)+(1+|T|)/N); on the intermediate
bands |G(T)| is bounded by a fixed source constant times (9). For ALL T,
the triangle inequality and the same quadrature applied to |rho| give

    |G(T)|<=J+o(1).

The absolute value is Lipschitz and has total variation at most integral
|rho'|, so its cellwise variation bound does not require it to be smooth.
More quantitatively, the error here is O_phi(1/(NW)+1/N).

Choose a(L)=(J/m0)kappa(L)+1=b log log L+1 and K=ceil(a)+1. Exactly the
same growing-order estimate (9) applies. Low frequencies use (10)--(11)
and quadrature; intermediate frequencies use the high-frequency energy
floor and (9). At high frequencies,

    |D(T)|/m <=2(J/m0)kappa(L)L+o(1),

because the triangle-bound quadrature error times kappa(L)L tends to zero.
Then log|T|>=a(L)L leaves margin 2L-O_phi(1). This proves MC4.
Every sum term with nonzero coefficient is an actual active node, even
when its coefficient is negative. Multiplying its exact null equation by
that signed coefficient remains legitimate. Summing the certificate
against the NONNEGATIVE mixture weights pays the energy margin exactly.

Status: **PAPER PROVED, LEAN OPEN**, novelty unestablished. It enlarges the
profile class within paired modulations; it is not a decomposition theorem
for arbitrary finite mixtures. Full PBAP still requires that missing
passage, or a direct certificate on the full null cone. Implement (10)--(11)
and the quantitative discrete estimates before claiming this in the corpus.

## Uniform-width candidate MC5

The signed implementation suggests using one common derivative schedule
for an interval of widths, rather than separate fixed/growing-width
capstones. This is a strengthening requiring its own quantifier audit,
not an inference from MC4's exact-width statement.

Fix a nonzero smooth complex unit-supported profile, kappa0>0 and
0<b<1/log2. Put m0=testMass(phi), J=integral |Re autocorr(phi)|>0.
For L=log(p)/2, allow EVERY W in

    kappa0 L exp(-L/2) <= W
      <= (m0/J)b L log log L exp(-L/2).                  (12)

Use the actual beta, m, signed G(T) and D(T) from MC4 at that W.
**MC5:** eventually, simultaneously for every W in (12) and every real T,

    e(T)+D(T) >= m L/2.

The resulting actual-null margin remains L/4 times physical mass, without
a correction-mass cap. The interval is nonempty eventually. Every fixed
positive kappa occurs eventually, so this would encompass the fixed-width
and growing-width statements, with arbitrary fixed complex profiles.

### Dependency and quantifier audit

Write kappa=W exp(L/2)/L and kappaMax=(m0/J)b log log L. The estimates in
MC4 use kappa's lower bound only in `NW` and `H^2 lambda`; its upper bound
only in the certificate cost and small-width remainders. Choose the SAME
`a=b log log L+1`, `K=ceil(a)+1` for all W, and eta=b log2<1.
Then `D_k<=8(log L)^eta` for every order used, independently of W.

On the adjacent bands, `4^k lambda<=L^(-1/4)` eventually as before.
Replace the other bound by

    H^2 lambda >= kappa0^2 L^(3/2)/(2pi 4^K) >= L.

Thus (9) holds uniformly for every permitted W. The Abel factor is O_phi(1/N),
while H/(NW) is bounded uniformly once NW>=kappa0 L sqrt N; no hidden
width-dependent constant is used. The low-height quadrature error is
O_phi,kappa0(L^(-1/2)), and its energy cost is at most O_phi,b(m sqrt L log log L).
The continuous leading term has

    -2log W >= L-2log L-2log kappaMax = L-o(L).

The pole remainder divided by m is bounded by O_phi,b((log log L)^3 L^3 exp(-L)).
The all-height triangle quadrature error multiplied by kappa L is uniformly
o(1): its `1/(NW)` part cancels kappa, and its `1/N` part is bounded by
kappaMax L/N. Finally the signed coefficient cost obeys
`|D(T)|/m<=2b L log log L+o(1)`, so the common high threshold `N^a` leaves
`2L-O_phi(1)` margin. The middle threshold is covered because K-a>=1.
The existing high-energy theorem uses a fixed lower-width parameter kappa0,
so its constants also remain uniform throughout (12). These facts prove
the stated eventual margin with one L0 for ALL W and T.

Paper argument closed; Lean implementation OPEN. The internal overlap
search completed; no scientific novelty claim is made. This is the proposed
unified capstone, not a change to the full PBAP target. No broad fixed-width
or arbitrary-mixture conclusion follows.

Internal audit: `research 'uniform width complex profile many node pole
certificate logarithmic interval' --mode deep --module Weil --budget-seconds
300 --json` exited0, partial=false, coverage68,806 files. All twenty candidates,
all source arguments, the proposed proof idea and ingredient set were
inspected. Most compiler metadata remains pending/source-only; refresh
reported a running background indexer, an older-generation coverage
snapshot and unavailable semantic coverage. Existing
uniform high-energy bounds are applicable support; ground-positivity and
`WeilPositiveFull` hypotheses in other hits would be unpaid/circular inputs.
The nearest-node phase identity does not prove a many-node width certificate.
The search also returned this agent's own new Gamma source, which is not
independent proof evidence. No prior closing capstone was identified; this
is not evidence of absence or a scientific-novelty claim.

A separate cached lexical L1/mass search located
`sq_integral_norm_le_of_abs_support` in `WeilMarginSuperexponentialLaw.lean` as a
classical Cauchy--Schwarz parent. A possible uniform-in-profile refinement
must still pay profile derivatives in the discrete transfer; it is not a
consequence claimed by MC5.
