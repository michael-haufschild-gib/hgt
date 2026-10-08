# A source-independent certificate on two narrow separated windows

Status, 8 October 2026: MC6 has a dependency-closed paper proof, including
the uniformity and normalization audit below. Lean OPEN; scientific novelty
unestablished. The tempting global completion is FALSE by the existing
Lean semiprime-floor obstruction (with a separate zeta interpretation below).
Its positive survivor is
MC6; the no-go is not closed until that survivor is formalized.

## Candidate and reason to investigate

MC4/MC5 still fix a source profile: their quadrature constants involve its
derivative. That prevents applying those theorems uniformly to unrelated
profiles in one aggregate-null mixture. A smooth cutoff equal to one on
the entire allowed correlation interval can move every derivative onto
one fixed auxiliary function. The source then enters only through Fourier
densities and exact mass.

Given the internal frontier, the stronger conjecture is a positive
restriction of ONE fixed completion to an entire two-window subspace.
Let `lambdaStar(n)=1+1/n` for n>=2, zero at 0 and 1, and

    Qstar(h)=testGamma(h)+testPole(h)-testAtoms(lambdaStar,h).

Choose one fixed even smooth cutoff psi, 0<=psi<=1, psi=1 on [-1,1],
support in [-2,2], and Apsi=integral psi. Fix b>0 with Apsi*b*log2<1.
Put

    N=exp L, kappa=b log log L, W=kappa L exp(-L/2).

**MC6:** for every sufficiently large L, every pair of smooth complex
functions f,g supported in [0,W] satisfies, for h=f+translate_L(g),

    Qstar(h) >= (L/4)*(testMass f+testMass g).             (U1)

The threshold must be independent of f and g. Their shapes, phases,
derivative norms and relative masses may vary arbitrarily with L.
Translation preserves mass and the two supports are disjoint, so the
quantity in parentheses is the actual mass of h.

If (U1) holds, nonnegative mixtures of these atoms may use DIFFERENT
profiles and different sufficiently large separations. Aggregate real
integer-nullness cancels the SAME lambdaStar pairing, so full energy has
the corresponding weighted mass margin. This would be a larger null cone
than paired modulations of one fixed profile. It still would not cover
arbitrary finite mixtures; positivity of every two-window restriction
does not prove positivity of all many-window matrices.

## Paper proof

Let alpha(y)=integral g(u) conjugate(f(u-y)) du; orient translation so the
positive-lag cross correlation of h is alpha(y-L). This orientation follows
by substituting u=x-L in the translated-first-source correlation. The other
cross term is conjugate(alpha(-y-L)). With the corpus positive-exponent
Fourier convention, the transform of alpha is F_g conjugate(F_f).
Write m_f=integral |f|^2, m_g=integral |g|^2, M=m_f+m_g.
Cauchy--Schwarz on support length W and convolution Fubini give

    integral |f| <= sqrt(W m_f),
    integral |g| <= sqrt(W m_g),
    integral |alpha| <= W sqrt(m_f m_g) <= W M/2.          (U2)

These are source-uniform and require no derivative bound.

### Exact cross poles and the fixed coefficients

The cross part of the literal two-pole expression is

    4 integral cosh((L+y)/2) Re alpha(y) dy.              (U3)

For W<log2 all diagonal integer samples vanish, and the negative-lag
cross term cannot meet a positive integer logarithm. Therefore

    testAtoms(lambdaStar,h)
      = sum_(n>=2) [4 cosh(log n/2)/n] Re alpha(log n-L).  (U4)

The equality uses exactly `logValue=2 Re autocorr(log n)/sqrt n` and
`2 cosh(log n/2)/sqrt n=1+1/n`. All sums are finite by support.
Unlike a coefficient frozen at L, (U4) is independent of the separation.

The diagonal pole terms have lower bound -O(W^3 M): subtract their
nonnegative zero-frequency squares and use cosh(y/2)-1=O(W^2) with (U2).

### Gamma cross term

The corpus formula `testGamma_eq_jump_scaled` and the preceding correlation
expansion give the literal cross Gamma term

    -2 integral J(2(L+y)) Re alpha(y) dy,

where J is `archJump`. Indeed the negative-lag term vanishes throughout
the positive jump integral; shift its remaining compact interval by L.
Since L>W, the absolute value is at most
`2 J(2(L-W)) integral |alpha|<=W J(2(L-W)) M`.
Thus Gamma(h) differs from Gamma(f)+Gamma(g) by o(M), uniformly in sources.
This is O(W exp(-L/2) M). Every shifted integral is away from the jump
singularity; the original diagonal integrals are paid by the existing
Gamma integrability theorem.

### A fixed complex Fourier quadrature error

Set

    v_(L,W)(y)=psi(y/W)*cosh((L+y)/2)/cosh(L/2),
    E_(L,W)(t)=sum_(n>=2) v_(L,W)(log n-L) exp(it(log n-L))/n
                 - integral v_(L,W)(y) exp(ity) dy.

The cutoff equals one on alpha's support. Fourier inversion and Fubini
express (U3) minus (U4) as a real pairing of `F_f conjugate(F_g)` with
`-4 cosh(L/2) E_(L,W)`. Its absolute integrand is bounded using

    2 |F_f F_g| <= |F_f|^2+|F_g|^2.

Consequently a sufficient scalar multiplier bound concerns

    gammaBracket(t)-2 cosh(L/2)*|E_(L,W)(t)|.             (U5)

All derivatives now fall on a uniformly bounded smooth compact family:
in scaled coordinates v(Wz)=psi(z)*cosh((L+Wz)/2)/cosh(L/2).
For W<=1 and |z|<=2, the hyperbolic ratio has absolute value at most e,
first derivative at most e W/2, and second derivative at most e W^2/4.
This follows directly from |sinh x|<=cosh x and
cosh(a+u)<=exp(|u|)cosh a. The product rule and the fixed first two
derivative norms of psi give uniform compact C2 bounds. The mean-value
theorem bounds the ratio's difference from one by eW, hence its L1 mass
is W*(Apsi+O(W)). No source derivative enters any constant.

Cellwise FTC gives |E(t)| <= C/N*(1+(1+|t|)W). Thus for
|t|<=N/sqrt L, `2 cosh(L/2)|E(t)|=O(kappa sqrt L)+o(1)=o(L)`.
On intermediate bands the short-prefix theorem plus Abel gives
`|sum|/W <= C exp(-c(log L)^(1-eta))`, eta=Apsi*b*log2<1,
with a common schedule K=ceil(Apsi*kappa+1)+1. The integral term has
inverse-square decay in Wt, uniformly for the same cutoff family.
Hence the same error in (U5) is o(L) for N/sqrt L<=|t|<=N^a,
where a=Apsi*kappa+1.
At |t|>=N^a, the triangle bound gives

    2 cosh(L/2)|E(t)| <= Apsi*kappa L+o(1),

because the continuous Fourier tail is already negligible. Meanwhile
gammaBracket(t)>=aL-O(1), leaving L-O(1).

### Uniform uncertainty floor

Let q=|F_f|^2+|F_g|^2. Exact Plancherel gives integral q/(2pi)=M,
and (U2) gives q<=WM pointwise. Use the fixed integrable log deficit
H(v)=1_(-1,1](v)|log v|, already formalized in `JointGammaFloor`.
For t!=0 the symbol satisfies

    gammaBracket(t)>=-log W-(10+log4)-H(Wt).

The low-band error is o(L); the middle/high lower bounds above dominate
`-log W-O(1)-o(L)` because -log W=L/2-o(L). Integrating (U5) against
q/(2pi), the H term costs only a universal multiple of M. Adding the
uniform Gamma-cross and diagonal-pole remainders would give

    Qstar(h)>=M*(L/2-o(L)) >= M L/4.

This proves (U1). It uses neither a positive-Weil
assumption nor a high-frequency bound with source derivative constants.

## Hostile audit and current limits

- Two-window positivity cannot be summed over all pairs without paying
  diagonal multiplicities. No full PBAP inference is licensed.
- MC6 does not assert that lambdaStar is a globally positive completion.
  Search that separate candidate for existing counterexamples/rigidity.
- The continuous Fourier multiplier must be complex: alpha need not be
  even or real. Replacing its error by a cosine-only estimate is invalid.
- The cutoff is auxiliary; it equals one wherever alpha is nonzero, so
  it changes neither the actual pole integral nor the finite atom pairing.
- Kernel orientation and uniform cutoff derivatives are paid above.
  Fourier Fubini is absolute: 2|F_f F_g|<=q and q is integrable, while
  the compact cutoff and its finite node sum have finite total variation.
  The Gamma-weighted integrals are separately integrable for each source;
  the log-deficit term is integrable by q<=WM and H in L1. These claims
  require formalization, not additional analytic premises.

The band constants are uniform: n=floor(exp(L-2W)),
m=ceil(exp(L+2W))+1 have n comparable to N and H=m-n comparable to NW.
The existing derivative bound gives `4^k lambda<=L^(-1/4)` and
`H^2 lambda>=L` throughout every adjacent band, uniformly k<=K.
Its explicit `2^k<=8(log L)^eta` dependence gives the displayed error.
The common top band covers N^a because K-a>=1. At high heights,
the O(W) correction to Apsi costs O(kappa L W)=o(1), and the quadrature
endpoint costs O(N^(-1/2)); the Fourier integral tail is also o(1).
Thus one nonnegative r(L)=o(L) bounds the low-band loss, while middle/high
symbols dominate `-log W-(10+log4)-r(L)-H(Wt)`.
The integrated H cost is `M*(integral H)/(2pi)`. Adding
`-W J(2(L-W))M` and `-W^3 M/2` proves the last inequality with a threshold
depending only on psi and b, including the zero-mass case.

Internal source-uniform search completed with partial=true and 68,809
indexed files; background refresh remained active and compiler metadata
mostly pending. All twenty candidates, source arguments and the proposed
ingredient set were inspected. Pole-residual and fixed-ground theorems do
not establish (U1); hypotheses `WeilPositiveFull` would be circular. No
closing result identified, with no absence or novelty inference.

Primary external audit: [Zhu v2](https://arxiv.org/html/2608.24827v2)
certifies a fixed compact window and documents a retracted larger-window
claim; it does not supply the separated-window certificate above.
[Connes--Consani](https://arxiv.org/abs/2006.13771) supplies a different
archimedean positivity framework. The abstract of the
[Suzuki-operator numerical study](https://arxiv.org/abs/2607.24830) was
inspected, without treating its numerical results as a proof of (U1).
No numerical experiment is used here. Scientific novelty remains unestablished.

Concrete cutoff for Lean: the existing real `RHTower.plateauBump` in
`ConstrainedWeilPlateauProfile.lean` gives psi(y)=plateauBump(4,y+2).
Its two smooth-transition factors exchange under y↦-y, so it is even;
the proved plateau/support/range facts give psi=1 on [-1,1], support
[-2,2] and 0<=psi<=1. Consequently 2<=Apsi<=4. The literal choice
b=1/(8 log2) is positive and has Apsi*b*log2<=1/2<1.
No cutoff-existence premise is needed. The existing `plateauProfile`
itself is ODD and is not the chosen cutoff. Its underlying `plateauBump`
is the relevant constructor. The first two derivatives have compact
support and are continuous, giving fixed finite derivative bounds.
`WeilWorkPBAPJointFixedCutoff.lean` now formalizes this constructor, uniform
C1/C2 bounds, the exact integral error at most `4e W^2`, and complex
inverse-square Fourier decay. Its 28 public theorem audits and final
direct-source check pass. The uniform growing-order proof is still required.

### Uniform order selection without individual band boundaries

A second paper proof of the middle-frequency schedule reuses the corpus
window-landing theorem, `exists_mem_window_of_ratio_lower_bound`, from
`HTGeometry/RatioBoundedWindowLanding.lean`. This is an implementation
refinement of MC6, classified BRIDGE; it asserts no new positivity result.
Keep the same actual integer interval, N=exp(L), H=m-n, a=Apsi*kappa+1,
K=ceil(a)+1 and U=(log L)/4. For positive t put

    lambda_k = t (k-1)! / (2pi (2n)^k),
    mu_k = 4^k lambda_k,
    B = 4^K exp(U)/H^2,       V = exp(-U).

For every m>2, `mu_m/mu_(m-1)=2(m-1)/n>=1/n`. Thus the existing
window-landing theorem supplies `2<=k<=K` with `B<=mu_k<=V` once

    B<=mu_2,   B<=V/n,   mu_K<=V.                     (U9)

The conclusion gives EXACTLY the short-prefix budgets:
`4^k lambda_k<=exp(-U)` and `H^2 lambda_k>=exp(U)`, since `4^k<=4^K`.
The normalized saving is at least `exp(-U/2^K)` for every selected order.

Here (U9) holds uniformly throughout `N/sqrt(L)<=t<=N^a` for large L.
Indeed n~N and H~4NW, while `mu_2=2t/(pi n^2)`. Therefore
`H^2 mu_2/exp(U)` is bounded below by a fixed positive multiple of
`kappa^2 L^(5/4)`. This dominates `4^K=O((log L)^(2eta))` and proves
the first condition. Likewise `H^2/n` is bounded below by a fixed
positive multiple of `kappa^2 L^2`, which dominates
`4^K exp(2U)=O((log L)^(2eta)*sqrt(L))`; this proves the second.

Finally n>=N/2 and K>=a+1 give
`mu_K<=4^K (K-1)!/(2pi N)`. Since `K=O(log log L)`, the elementary
factorial bound implies
`log(4^K (K-1)!)=O((log log L)^2)=o(L)`.
Thus this last upper bound is eventually at most `exp(-L/2)/(2pi)`,
which is below `exp(-U)`. The order bound `2^K<=8(log L)^eta` remains
unchanged. All three threshold choices depend only on psi,b.

This proof avoids requiring a sharp factorial estimate on every separate
frequency band. It still retains the actual short length H; the corpus's
dyadic saving window cannot replace (U9). The floor/ceiling interval
estimates and the uniform eventual inequalities are still Lean obligations.

The interval geometry in this argument has an explicit elementary budget.
Write `Cgeo=4e+3`. If `N>=4`, `NW>=1`, `0<W<=1/8`, and `Cgeo*W<=1/2`,
then the actual choices `n=floor(N exp(-2W))`,
`m=ceil(N exp(2W))+1` satisfy

    2<=n,   N/2<=n<=N,   2NW<=H<=Cgeo*NW,   n<m<=2n+1.

Indeed `exp(-2W)>=1-2W` and the floor error give
`n>=N(1-2W)-1>=N/2`. The exponential difference is at least 2W,
using `exp(2W)>=1+2W` and `exp(-2W)<=1`, so `H>=2NW`.
The mean-value theorem on [-2W,2W] gives an upper difference of 4eW.
Rounding at BOTH ends and the additional right endpoint cost at most
THREE units, whence `H<=4eNW+3<=Cgeo*NW`. Finally this is at most
N/2<=n, giving the dyadic containment. All these explicit side conditions
hold eventually for the MC6 width. In particular no endpoint rounding
error is absorbed into an unsupported equality `H=4NW`.

`WeilWorkPBAPJointGridGeometry.lean` now formalizes this explicit geometry
and discharges its side conditions at the actual width for every b>0,
eventually in L. The logarithmic endpoints enclose [-2W,2W]. All six
public source/axiom audits pass; the order-selection inequalities remain.

For the formal schedule, the same argument allows the stronger choice
`U=(log L)/2`. Put R=sqrt(L), so exp(U)=R. The ceiling-order estimate
gives `4^K<=R` eventually, since every fixed power of log L is o(sqrt L).
The geometry gives `H^2>=4 kappa^2 L^2 N>=4 b^2 L^2 N` and n<=N,
once log log L>=1. At t>=N/R, `mu_2>=2/(pi N R)`; hence

    H^2 mu_2 >= (8/pi)b^2 L R >= L >= 4^K exp(U)

when R>=(pi+1)/b^2. The same threshold gives

    H^2 >= 4 b^2 L^2 N >= N L R >= n 4^K exp(2U).

These are the first two conditions of (U9), with their actual constants.
For the last, the factorial estimate already gives
`mu_K<=exp(-L/2)/(2pi)`. Since `R exp(-L/2)<=2pi` eventually, this is
at most 1/R=exp(-U). The strengthened choice only improves the saving
constant; the admissible eta<1 and MC6 width are unchanged. This is a
paper-level audit of the stronger intermediate statement before Lean
implementation, not a new positivity capstone.

The complete growing-order scratch now passes Lean (24.65s), including
all three actual budgets and every-prefix cancellation with explicit
factor `exp(-(log L)^(1-c log2)/16)`. The new production leaf
`WeilWorkPBAPJointGrowingOrder` passed its targeted build, final direct
source audit and all nine standard-only axiom checks. This closes the numerical schedule obligation;
the MC6 energy gluing remains open.

The subsequent middle-cutoff scratch passes66.03s. With one absolute C,
the actual fixed-cutoff Abel variation gives `|grid(t)|<=C W saving`
throughout the middle band, for both signs of t. The continuous term obeys
`|Fourier(v)(t)|<=C exp(-L)` already for `|t|>=N/sqrt(L)`: eventually
`b log log L>=1` gives `WN>=L`, while `L t^2>=N^2`, hence `Wt^2>=N`.
The previously audited inverse-square Fourier estimate pays this bound.
Thus the actual complex error is at most `C(W saving+exp(-L))`.
Its exact `2 cosh(L/2)` multiple is o(L), since eta<1 makes
`log log L * saving` tend to zero. The production leaf is wired and all
eleven public source/axiom audits pass;
the low/high joins and literal source-energy identities remain open.

The grid-frequency scratch now passes55.66s. It proves the full complex
quadrature bound, a nonnegative o(L) low-band loss, and
`|E(t)|<=Apsi W+C(W^2+exp(-L))` above N/sqrt(L). Its paid high remainder
leaves `2 cosh(L/2)|E(t)|<=log|t|-3L/4` above the growing ceiling.
The production leaf is wired; all twelve public source/axiom audits pass.
The audited `JointSymbolFloor` Gamma join uses the same deficit H and the eventual bounds
`3L/8<=-log W<=L/2`. After integration, choose the o(L) loss and fixed
deficit constant each at most L/48. This leaves L/3 times each source's
actual mass, reserving L/12 for the remaining cross-Gamma and diagonal
pole losses before MC6's L/4 conclusion. These choices make the previously
paper-closed o(L) bookkeeping explicit; no stronger PBAP claim follows.
Its nine public audits pass, including the literal b=1/(8 log2) two-source
corollary. The support, energy and null identities remain the next obligations.

For the next exact-source leaf, a weaker sufficient L1 bound avoids any
extra convolution inequality: pointwise AM-GM and translation invariance give
`2|alpha(y)|<=m_f+m_g`. The support is contained in [-W,W], so integrating
gives `integral|alpha|<=W*(m_f+m_g)`. This doubles the displayed sharp
remainder constants, without changing their o(L) conclusion or MC6's L/4
margin. At y=0 the cross terms vanish when L>W, proving exact mass additivity.
Translation in the convolution integral and complex conjugation prove the
four-term correlation expansion above for arbitrary complex f,g. This is a
BRIDGE, not an independent novelty claim.

The corresponding sufficient remainder bound is exact: the Gamma cross
error is at most `2 W J(2(L-W)) M`. On the positive half-line, its integrand
is `J(2y) Re alpha(y-L)`; nonzero correlation forces `y>=L-W`, and J is
decreasing on positive arguments because its positive numerator decreases
while its positive denominator increases. Integrate the absolute value,
enlarge to the full line, translate, and use the preceding L1 bound.
For a diagonal source, `integral Re autocorr=|integral f|^2>=0`.
On its support, `|cosh(y/2)-1|<=W^2/4` for W<=1. The same L1 bound with
f=g therefore gives `testPole(f)>=-W^3*m_f`. These paid bounds suffice
for MC6, with no sign assumption on any source correlation. The sharper
exponential decay needed by the many-window extension follows directly
from the retained exact J factor.

## Global lambdaStar fails: retain the local survivor

The strongest internal rejection needs no external large-value input:
`RHTower.WeilAbscissa.not_weilPositiveFull_of_nonneg_semiprime_floor` in
`WeilConeMultiplesOfPrimeLaw.lean` excludes every nonnegative weight with
a fixed positive floor on pq for a fixed prime p and all other primes q.
Here take p=2,c=1. The hypotheses follow from lambdaStar(n)>=1 for n>=2.
No size bound or coefficient-integrality assumption is needed. Exact
scratch instantiation `/tmp/wp01-grid-obstruction.lean` and axiom audit
PASS60.53s, exit0; only propext/Classical.choice/Quot.sound. This is an
application of a known corpus obstruction, not a new scientific theorem.
Its corpus search completed with partial=false,68,814 indexed files,
background refresh and compiler metadata pending; all returned candidate,
source-argument and ingredient entries were inspected before checking the
decisive source and this literal Lean instantiation.

The existing WP02 `GRID-DEFECT-PROOF.md` already proves the critical-line
zeta content of integer pole quadrature. Its principal-defect argument,
plus the absolutely convergent n^(-3/2) correction, gives for every smooth
compact h the exact identity

    Qstar(h)=(1/(2pi)) integral |F_h(t)|^2 S(t) dt,
    S(t)=gammaBracket(t)+4-2 Re zeta(1/2+it)-2 Re zeta(3/2+it). (U6)

The constant4 is the omitted n=1 term, whose coefficient is2 before the
outer factor2. For a finite principal defect, pair first with |F_h|^2;
the compact autocorrelation makes the node sum eventually finite and
constant. The existing error O((1+|t|)/sqrt K) is integrable against this
density, paying the limit. The n^(-3/2) term is absolutely summable.
This derives (U6), rather than assuming a distributional interchange.

At positive-real zeta peaks,
[Kalpokas--Korolev--Steuding, Corollary3](https://arxiv.org/html/1109.2224)
gives Re zeta(1/2+it)>c(log T)^(5/4) at some t<=T. Gamma is O(log(2+T))
and |zeta(3/2+it)| is bounded, so S(t)<0 at arbitrarily large heights.
Only the unconditional part of that corollary is used. The symbol is
continuous and has polynomial growth (the same principal-defect bound
already gives a linear bound for the critical-line real part).

Fix one negative point t0 and a nonzero smooth compact bump phi. The tests
`h_R(x)=R^(-1/2)phi(x/R)exp(-it0 x)` have Fourier-square densities forming
an approximate identity at t0. After t=t0+v/R, Schwartz decay of F_phi
dominates the polynomial symbol bound; dominated convergence makes
Qstar(h_R)/testMass(h_R) tend to S(t0)<0. Some actual compact test therefore
has negative Qstar. This rejects GLOBAL positivity of lambdaStar, without
producing a PBAP-null counterexample.

Verdict: the global-grid obstruction is REDISCOVERED from existing corpus
results. The semiprime-floor proof is internal; the alternative zeta
interpretation is paper-only because the external large-value theorem is
not formalized here. MC6 remains compatible: narrow two-window sources cannot freely
localize at the bad multiplier peaks. The positive survivor is a uniform
restriction of this indefinite completion to every allowed two-window
subspace, plus arbitrary aggregate-null mixtures of those atoms. Its
paper proof is above; exact Lean formalization is the next obligation.

## MC7: an unbounded number of widely separated narrow windows

This is a BRIDGE from MC6, not an independent novelty claim. It pays the
diagonal multiplicity that prevents a naive sum of two-window inequalities.
Fix the same psi,b as MC6. For all sufficiently large D, put
W=b D log log D exp(-D/2). Let r>=2 and

    0=x_0<x_1<...<x_(r-1)=D,
    x_(j+1)-x_j >= 6 log D.

For arbitrary smooth complex f_j supported in [0,W], put
h(x)=sum_j f_j(x-x_j) and M=sum_j testMass(f_j). Then the paper argument gives

    Qstar(h) >= (D/5) M.                               (U7)

The threshold is independent of r, locations, shapes, phases and masses.
In particular r may grow to order D/log D. The same lambdaStar permits
aggregate-null mixtures of these atoms at different diameters. Lean OPEN.

To prove it, set m_j=testMass(f_j) and R_ij=sqrt(m_i m_j). For a pair at
distance d=x_j-x_i, let alpha be its cross correlation. Cauchy--Schwarz
gives |alpha(y)|<=R_ij pointwise and integral|alpha|<=W R_ij. When W<=1
and d>=2, the cross contribution of Gamma is bounded in absolute value
by C W exp(-d/2)R_ij, by the same jump formula as above. Its pole
contribution is at most C W exp(d/2)R_ij.

Every active positive integer lies in [exp(d-W),exp(d+W)]. This interval
contains at most exp(d+W)-exp(d-W)+1 <= 2e exp(d)W+1 integers. Each
coefficient 2 lambdaStar(n)/sqrt(n) is at most 4 exp(-(d-W)/2).
Thus the actual atom contribution, with its full finite node set, is at
most C[W exp(d/2)+exp(-d/2)]R_ij. No quadrature or source derivative is
used in this bound. Combining the three contributions bounds the full
cross term by that same expression with one larger universal C.

Keep the unique extreme pair (0,r-1) together and use MC6 on it. Every
other pair has 6 log D<=d<=D-6 log D. Also r<=1+D/(6 log D)<=2D for
large D, and

    sum_(i<j) R_ij <= (r-1)M/2 <= D M.

Consequently all remaining cross terms together have absolute value at
most C[(b log log D)/D+D^(-2)]M=o(M). This estimate includes interactions
of an interior window with either extreme, and all interior-interior
interactions; none is discarded. If r=2 the remainder sum is empty.

Every isolated interior source has zero integer atom pairing once W<log2.
The source-uniform Gamma floor and the diagonal pole remainder give

    Qstar(f_j)>=[-log W-C-W^3/2]m_j >= (D/3)m_j

eventually, uniformly in j. MC6 gives D/4 times the extreme-pair mass.
Adding these diagonal and cross terms proves (U7) for one common threshold.
Disjoint supports give testMass(h)=M, including zero-source cases.

Hostile checks: this is not arbitrary many-window positivity; dropping
the separation condition invalidates the remainder estimate. Pairwise
positivity alone is insufficient; the unique longest pair and the paid
sum of every shorter interaction are essential. It does not contradict
the global semiprime obstruction and does not solve full PBAP.

Internal sparse-window hybrid search returned partial=true (68,822 files)
and no candidates; the broadened lexical OR query returned only an
unrelated zero-count window-sum theorem. No absence claim follows.
External follow-up opened [Burnol's support-positivity abstract](https://arxiv.org/abs/math/0101068)
and [Connes--Consani's spectral-triples paper](https://ems.press/content/serial-article-files/44477?nt=1).
Their inspected material does not establish this fixed-lambdaStar sparse
restriction; no new parent theorem is imported from those reads. MC7 is
classified BRIDGE because the argument above is a direct extension of MC6.
Complete MC6's Lean proof before implementing this enlargement.

### MC8 refinement: pay geometric row sums, not the number of windows

MC7's factor r is unnecessary. The stronger paper survivor replaces its
spacing by

    delta(D)=4 log log log D,
    x_(j+1)-x_j >= delta(D),                            (U8)

for sufficiently large D, with the SAME width and D/5 mass margin. This
allows order D/log log log D windows. Verdict BRIDGE from MC6 and the
elementary Schur row-sum bound; not a separate novelty claim. Lean OPEN.

Here is the uniform argument, including the growing number of windows.
Put q=exp(-delta/2). Delete only the extreme pair from the interaction
matrix. In any fixed row, distances to successive windows in either
direction increase by at least delta. Every retained distance is between
delta and D-delta. Summing the two geometric progressions gives

    sum_j exp(-d_ij/2) <= 2q/(1-q),
    sum_j exp(d_ij/2) <= 2 exp(D/2)q/(1-q).

The bounds hold after deletion of the extreme pair, including the extreme
rows; there the removed farthest term makes the largest retained distance
at most D-delta. The pairwise estimate in MC7 therefore bounds each row
sum of absolute cross coefficients by

    C [W exp(D/2)+1] q/(1-q).

For symmetric nonnegative coefficients a_ij, the inequality
`2 sqrt(m_i m_j)<=m_i+m_j` gives
`sum_(i<j) a_ij sqrt(m_i m_j)<= (max row sum) M/2`.
This pays EVERY retained interaction without a factor r.
With delta as in (U8), q=(log log D)^(-2), while
W exp(D/2)=b D log log D. The total cross cost is thus
O(D/log log D)M=o(D)M, uniformly in the number and positions of windows.
Keep MC6's D/4 bound on the extreme pair and D/3 on each interior
diagonal as before. Subtracting this o(D)M cost proves D/5 times M.

The broader sufficient budget is `(1+kappa D)exp(-delta/2)/(1-exp(-delta/2))=o(D)`.
It identifies the relevant interaction loss as the width surplus kappa
times a geometric spacing factor. This refinement is forced by auditing
the multiplicity cost in MC7; it remains a restricted sparse-support
theorem, not a construction of a global positive lambda or full PBAP.
The earlier sparse-window searches and external parent audit apply;
the new step is explicitly classified as the classical row-sum bridge.
