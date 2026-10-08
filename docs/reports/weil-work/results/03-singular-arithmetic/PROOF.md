# WP03 proof record

## Sharp cancellation of the actual reciprocal coefficients

Let λ be full-cone Weil-positive and λ₀(n)=λ(n) for n≥2, zero otherwise.
Write μλ=producerMobius(λ₀). For every ε>0 there exists C≥0 such that

    |Σ_{n≤N} μλ(n)| ≤ C (N+1)^(1/2+ε)     (N∈ℕ).

No additional regularity, coefficient bound, zero-free or summability assumption
is imposed on λ. Full positivity supplies absolute convergence for Re s>1,
the literal reciprocal continuation G, and its subpolynomial strip growth.

Choose q=min(ε/4,1/4), a=q/2, δ=q, c=1/2+δ. Then 0<a<q≤1,
0<δ<1/2, c≤2 and c+q≤1/2+ε. Existing reciprocal strip bounds give K≥0
with |G(s)|≤K(2+|Im s|)^a throughout c≤Re s≤2.

For integer N≥1 use the existing smooth cutoff with onset N and transition
width H=1/2. Its values on integers are exactly the sharp cutoff: all positive
integers ≤N have value 1, all integers >N have value 0. The coefficient at zero
is zero. Therefore its weighted infinite sum is the desired finite sum exactly.

The absolutely convergent Mellin inversion on Re s=2 equals 2π times this sum.
The existing contour-shift theorem moves the integral to Re s=c; its strip
growth and rapid Mellin decay pay both horizontal edges and line integrability.
The fractional Mellin mass theorem bounds the norm of the shifted integral by

    2K 3^a (N+H)^c/c
      + 2K 3^a P ((N+H)/H)^q (N+H)^c/(q-a),

where P=C₀^(1-q) C₁^q and C₀,C₁>0 are the existing universal Mellin constants.
Since N+1/2≤N+1 and (N+1/2)/(1/2)≤2(N+1), this is at most

    [2K3^a/c + 2K3^a P 2^q/(q-a)] (N+1)^(1/2+ε).

Divide by 2π. N=0 follows from μλ(0)=0. This closes the paper proof.

## Stronger all-height reciprocal estimate

The same proof gives a constant Cε, independent of N and t, such that

    |Σ_{n≤N} μλ(n)n^(-it)| ≤ Cε (N+1)^(1/2+ε) (2+|t|)^ε.

There is no exceptional set. At n=0 define the twisted coefficient to be
zero, consistent with μλ(0)=0. For fixed t, twist the coefficients by
n^(-it) and use Gt(s)=G(s+it). Their absolute values are unchanged for
n≥1, so Perron's absolute-convergence premise is unchanged. The complex
power addition law identifies the right-edge series with Gt exactly.
The imaginary translation preserves the strip and holomorphy.

Since 2+|y+t|≤(2+|y|)(2+|t|), the previous strip bound becomes
|Gt(s)|≤[K(2+|t|)^a](2+|Im s|)^a. Every Mellin bound above is linear
in K. It therefore gives the same numerical constant multiplied by
(2+|t|)^a, which is ≤(2+|t|)^ε because a=q/2≤ε. No translated zeta
factor occurs in this argument. Unlike the prospective quotient estimate,
this reciprocal estimate is uniform for all real t with its displayed
subpower loss. It still does not bound ζG uniformly in height.

## Research calibration

This is a bridge using classical Perron analysis, not a claim of new mathematics
beyond the literature. It strengthens the located corpus statement from a wide
smooth cutoff to the actual ordinary sums without importing |μλ(n)|≤1.
The uniform zeta-quotient bound remains open. Ordinary cancellation alone does
not control the exceptional vertical orbit.

## Consequences and next conjecture

For each s with Re s>1/2 choose ε=(Re s-1/2)/2. The sharp estimate and the
existing polynomial Abel theorem give ordinary convergence of
Σ μλ(n)n^(-s). On the domain Re s>1/2 these sums are holomorphic: at each
point choose a strictly smaller real abscissa still above 1/2, and apply
the existing locally uniform Abel convergence theorem. On Re s>1 the sum
is G by absolute convergence; the identity theorem identifies it with the
same literal reciprocal throughout Re s>1/2. In particular, at s=1 its
ordinary harmonic sum is zero, since the reciprocal has its simple zero there.

Prospective quotient bridge (paper only; not yet claimed as a new formal result):
write qλ=1*μλ and M(x)=Σ_{n≤x}μλ(n). For Y between 1 and x, the exact
hyperbola split gives

    Σ_{n≤x} qλ(n)
      = Σ_{d≤Y} μλ(d) floor(x/d)
        + Σ_{m≤x/Y} [M(x/m)-M(Y)].

The harmonic sum zero and Abel tail bound make the first term
O(xY^(-1/2+η)+Y^(1+η)); absolute convergence of the reciprocal for
Re s>1 supplies Σ_{d≤Y}|μλ(d)|=O(Y^(1+η)). The second term is
O(xY^(-1/2+η)). Taking Y=x^(2/3) gives O(x^(2/3+ε)). This is classical
hyperbola analysis and is classified BRIDGE, not significant novelty.

The bold next target is the square-root exponent for qλ, then uniform twisted
control. The hyperbola proof loses cancellation in Σ_{d≤Y}μλ(d){x/d}.
That literal floor-fractional-part correlation is an exact unpaid arithmetic
quantity; no average-over-twists statement pays it automatically.

## Exact uniform strengthening that pays the existing receiver

An adequate strengthening concerns qλ, not μλ: for every α>1/2 require
a constant Cα such that

    |Σ_{n≤N} qλ(n)n^(-it)| ≤ Cα N^α   for all N≥1 and all real t.

This is an unpaid target, not an assumption of the proved bridge. For x>1/2
choose α strictly between 1/2 and x, with α<1. Apply ordinary real Abel
summation to the coefficients qλ(n)n^(-it). For σ>x the series has bound
Cα σ/(σ-α), uniformly in t. The boundary term vanishes and the integral is
absolutely admitted by α<σ. Since σ/(σ-α)≤x/(x-α), the same constant works
on the entire half-plane σ>x. Locally uniform convergence identifies the
sum with the holomorphic removal of ζG at s=1, using the exact product
identity on Re s>1 and uniqueness of analytic continuation. Thus the
literal G and this bound satisfy `riemannHypothesis_iff_exists_bounded_zetaQuotient`.

An untwisted bound only permits complex Abel summation with a factor |s|;
it does not give the displayed uniform bound. The missing uniformity is
explicit, not hidden in an exceptional set or an almost-everywhere statement.

## Cycle 2: square-root quotient sums via the actual contour

Define qλ literally by `LSeries.convolution 1 (producerMobius λ₀)`. The
right-half-plane product identity follows from `LSeries_convolution'`,
`LSeries_one_eq_riemannZeta`, and `LSeries_producerMobius`. Absolute
convergence for Re s>1 follows from `LSeriesSummable.convolution`.

Use the primitive reciprocal G(s)=c(s−1)exp(P(s)) and the pole-removed
quotient Q(s)=c zetaEntire(s) exp(P(s)). Thus Q is holomorphic on Re s>1/2
and equals ζ(s)G(s) away from 1. This is exactly the construction already
used in `WeilProducerZetaQuotientBohrRecurrence.lean`, lines 395–418.

Fix ε>0 and set q=min(ε/4,1/4), a=q/2, c₀=1/2+q. The existing reciprocal
bound is |G(c₀+it)|≤K(2+|t|)^a. The existing unconditional theorem
`exists_integral_normSq_zeta_vertical_le` bounds each dyadic positive-height
block by C T(1+log T)^3, uniformly for 1/2≤c₀≤3. Cauchy–Schwarz gives

    integral_T^(2T) |ζ(c₀+it)| dt ≤ sqrt(C) T(1+log T)^(3/2).

Conjugation gives the negative-height version. Consequently

    integral_{|t|≥1} |Q(c₀+it)| |t|^(-1-q) dt < infinity:

the blocks T=2^j, j≥1, are bounded by a constant times
2^(j(a−q))(1+j)^(3/2), a summable geometric-polynomial sequence. The
remaining compact intervals are admitted by continuity, since c₀<1.
This is a global integral for the actual untwisted quotient, not a
statement for Haar-almost-every twist.

For H=1/2, X=N+H, R=X/H, the small-height Mellin bound is X^c₀/c₀,
and the fractional large-height bound is P R^q X^c₀ |t|^(-1-q).
Multiplying by Q and integrating therefore costs O(X^c₀(1+R^q)), hence
O((N+1)^(1/2+ε)). On the whole strip from c₀ to 2, Q has a polynomial
height bound: use the existing polynomial ζ bound and reciprocal bound
off |t|≤1; use continuity of the pole-removed Q on the compact remainder.
The existing smooth Mellin contour shift therefore applies. Perron and
the exact width-1/2 integer cutoff give

    |Σ_{n≤N} qλ(n)| = Oε((N+1)^(1/2+ε)).

This closes the analytic paper argument, replacing the weaker hyperbola
estimate. Lean status: formalized and audited in the weighted-zeta, Mellin-mass,
and quotient leaves. All three final direct audits passed; EVIDENCE.md records
the exact declarations and standard-axiom audit.
Verdict: BRIDGE; classical second-moment/Perron parent, no scientific
novelty claim. It still does not yield the bound uniformly after replacing
qλ(n) by qλ(n)n^(-it₀): the weighted integral is then centred at t₀, and
the above constant depends on t₀. Treating it as uniform would assume the
exceptional-height control that WP03 must prove.

### Formal assembly details for cycle 3

For the weighted zeta admission one may replace Cauchy–Schwarz by the
elementary inequality u≤1+u². Thus the dyadic first moment is at most
(1+C)T(1+log T)^3. On T=2^(j+1), weighting by t^(-1-η) gives a majorant
D(j+1)^3 r^(j+1), r=2^(-η)<1. The cells [2^(j+1),2^(j+2)] cover [2,∞),
so summability proves integrability. On σ≠1, continuity admits [-2,2];
ζ(conj s)=conj ζ(s) reflects the positive ray. Replacing t by 2+|t| gives
the globally continuous weight (2+|t|)^(-1-η).

Fix c>0 and 0≤q≤1. The existing two-scale Mellin constants define
P=C₀^(1-q)C₁^q. Put D=3^(1+q)(1/c+P 2^q). For every integer N≥1,

    |Mellin(smoothWeight(N,1/2))(c+iy)|
      ≤ D (N+1)^(c+q) (2+|y|)^(-1-q).

For |y|≤1 use the small-height bound (N+1/2)^c/c and 2+|y|≤3.
For |y|≥1 use the fractional bound P[2(N+1/2)]^q(N+1/2)^c |y|^(-1-q)
and 2+|y|≤3|y|. The inequalities N+1/2≤N+1 and N+1≥1 absorb both
powers into c+q. Thus an integrable norm profile
J=integral |F(c+iy)|(2+|y|)^(-1-q) dy bounds the entire Mellin mass by
D J (N+1)^(c+q). Polynomial strip growth supplies the contour shift;
the weighted mass controls its size. These are separate obligations.

## Next conjecture: actual quotient square mass (OPEN)

For qλ=1*μλ, conjecture that arbitrary full positivity gives

    ∀ε>0 ∃Cε≥0 ∀N, Σ_{1≤n≤N}|qλ(n)|² ≤ Cε(N+1)^ε.

This is not an assumption of any new Lean result. Its proof from full positivity
is the OPEN CORE. No paper proof of that implication is claimed.

The implication to the detector is dependency-closed at the analytic level:
fix σ>1/2 and choose 0<ε<2σ−1. On a dyadic block [2^k,2^(k+1)),
Cauchy–Schwarz bounds the sum of |qλ(n)|n^(-σ) by a constant times
2^(k*(1/2+ε/2−σ)). The resulting geometric series converges. Thus the quotient
Dirichlet series converges absolutely on every strict right critical half-plane;
its analytic function agrees with the pole-removed ζG on Re s>1 and hence,
by analytic uniqueness, on Re s>1/2. Given x>1/2, choose σ strictly between
1/2 and x. The absolute σ-sum bounds all values with Re s>x, uniformly in
height. The existing bounded-quotient receiver then applies. This sufficient
implication is classical; the conjectured source square law is the unproved part.

### Attempt to kill the inference from cancellation alone

Take G(s)=1−2^(1−s), μ(1)=1, μ(2)=−2 and μ(n)=0 otherwise. Then
q(n)=(1*μ)(n)=(-1)^(n+1) for n≥1. Every signed prefix has magnitude at most1,
while Σ_{n≤N}|q(n)|²=N. G is entire, vertically bounded on each fixed strip,
and vanishes at1. It even has the required far-right exponential shape for the
weights lam(2^k)=2^k log2 (k≥1), zero at other integers: expanding
−log(1−2^(1−s)) gives precisely Σ lam(n)/(log n)n^(-s) on Re s>1.

This is not a full-positive system. G also vanishes at
1+2πik/log2 for every integer k, contradicting the zero classification of the
actual full-positive reciprocal. Its weights also exceed the full-cone square-root
coefficient envelope. Consequently this example kills a proposed implication
from ordinary cancellation plus elementary strip bounds to square-mass control;
it does not kill the conjecture from full positivity. This calculation is an
exact paper countermodel, not a numerical experiment or a newly claimed theorem.

### Candidate arithmetic mechanism and unpaid step

The far-right quotient logarithmic derivative gives the coefficient recurrence

    (log n)qλ(n) = Σ_{d|n}(Λ(d)−lam'(d))qλ(n/d).

Multiplying by conjugate(qλ(n))/n and summing produces the full triangular
divisor interaction, with diagonal energy Σ(log n)|qλ(n)|²/n. A Weil test made
from translated packets at log n with amplitudes qλ(n)/sqrt(n) has the matching
integer-ratio interaction weights. A proof must estimate the complete packet
form before any limiting operation. Dropping cross terms, replacing the actual
height orbit by independent phases, or taking a singular point-packet limit
without its archimedean cost would be invalid. There is currently no proved
coercive estimate for that complete form. Existing logarithmic convolution
calculus is parent machinery, not evidence that coercivity holds.

### Sign audit of the first packet substitution

The existing `weil_multiplicativeToeplitz_bound` supplies
2 I_lam(c)≤(log N+C0)Σ|c_n|². Put c_n=qλ(n)/sqrt(n) for 1≤n≤N and zero
otherwise, and write

    S_N = Σ_{n≤N}|qλ(n)|²/n,
    E_N = Σ_{n≤N}(log n)|qλ(n)|²/n,
    I_a = Re Σ_{dm≤N, d≥2} a(d)qλ(m)conjugate(qλ(dm))/(dm).

The recurrence gives E_N=I_Λ−I_lam. Substitution into the proved bound yields

    2 E_N ≥ 2 I_Λ − (log N+C0) S_N.

This is a LOWER bound for E_N. It does not give the upper mass control sought
in the conjecture. Large reciprocal energy makes this particular positivity
test easier to satisfy. Reversing the inequality would be an error. Thus the
first direct packet-substitution strategy fails to deliver coercivity. The
square-law conjecture itself remains open; a successful proof needs another
use of the full form or a coupled test retaining information discarded by this
one-sided Toeplitz consequence.

The corpus already controls Σ_{N<n≤2N}lam(n)² by
2N(log(2N)+C0)². Dividing by n and summing dyadically yields a cubic-logarithmic
prefix bound for Σlam(n)²/n, hence Booker's subpolynomial square-prefix condition
for f(n)=lam(n)/sqrt(n). This is parent evidence to reuse, not a new finding.
It does not transfer through the nonlinear reciprocal exponential to qλ.

## Paper classification: subcritical absolute quotient convergence forces Λ

Status: complete paper argument using the classical ordinary-Dirichlet Wiener
inverse theorem; NOT formalized in Lean. This is a reduction to an existing
regularity theorem, not the requested unconditional source estimate.

Suppose hW is full positivity and Σ|qλ(n)|n^(-a)<∞ for some a<1. Choose
max(a,1/2)<b<x<y<1. The absolutely convergent quotient series is holomorphic
on Re s>a and agrees with the existing pole-removed Q=ζG on Re s>1, hence
on Re s>max(a,1/2). On Re s>b its absolute a-sum bounds its norm. The exact
quotient receiver therefore excludes ζ zeros on Re s>b. The primitive form
G=κ(s−1)e^P has no other zeros and κ≠0; Q(1)=κe^{P(1)}≠0. Thus Q is zero-free
throughout Re s>b.

Q is bounded away from zero on Re s≥x. To see this, suppose otherwise. Its
far-right limit is1, uniformly in height, so a sequence of small values has
real parts in a fixed compact interval [x,R]. Absolute Dirichlet convergence
makes all vertical translates a relatively compact family, uniformly on each
half-plane Re s≥b'>b (finite heads plus a uniform absolute tail). Pass to a
subsequence of translates and real parts. The limiting holomorphic function
has a zero inside Re s>b, but is not identically zero since its far-right limit
remains1. Every translate is zero-free there, contradicting Hurwitz's theorem.
This proves a positive lower bound without a zero-free hypothesis added to hW.

Apply the Hewitt–Williamson inverse theorem to the shifted absolutely convergent
series Q(x+s). The Dirichlet coefficients of 1/Q are absolutely summable at x.
Termwise differentiation of Q is absolutely admitted at y because log n is
absorbed by n^(y−x). Dirichlet convolution then makes Q'/Q an absolutely
convergent ordinary Dirichlet series at y. On Re s>1, the literal exponential
identity gives

    Q'(s)/Q(s) = Σ_{n≥2}(lam(n)−Λ(n))n^(-s).

Uniqueness of absolutely convergent Dirichlet series identifies every coefficient;
the zero coefficient is immaterial and the coefficient at1 is zero. Consequently
Σ|lam(n)−Λ(n)|n^(-y)<∞ on n≥2. Adjusting the two finite initial terms gives the
exact hypothesis of `WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable`.
Since y<1, that theorem proves lam(n)=Λ(n) for every n≥2.

Conversely, normalized lam=Λ gives μλ=μ and qλ=δ1 by the literal exponential
identity and Dirichlet coefficient uniqueness, so its absolute series converges
everywhere. Thus this absolute-quotient class contains no new positive producer.
The conjectured subpolynomial qλ square prefixes imply membership in this class
by the dyadic argument above, so proving that conjecture for every hW would prove
full arithmetic uniqueness. This explains why the easier-looking square law
still encounters the closed regularity wall.

Primary source: Deutsch, *Deux remarques sur les séries et les polynômes de
Dirichlet*, AIF24(3),1974, pp165–169, states the Hewitt–Williamson theorem on
p166: https://aif.centre-mersenne.org/item/10.5802/aif.524.pdf.
The modern weighted inversion result at
https://articles.math.cas.cz/10.21136/MB.2026.0072-25 does not remove the
bounded-away-from-zero requirement. No external theorem is being treated as a
Lean axiom, and no paper-only step is used by the audited quotient leaves.
## Cycle 5: reciprocal and quotient square mass (paper proof)

For arbitrary full positivity and every ε>0, both μλ and qλ=1*μλ satisfy
Σ_{1≤n≤N}|a(n)|²=Oε((N+1)^(1+ε)). This is a classical mean-value bridge
from the newly audited all-twist reciprocal bound; it does not establish a
bounded mean for the infinite series or any uniform quotient bound.

**Reciprocal.** Put δ=ε/4. The proved all-twist bound gives
|P_N(t)|≤C(N+1)^(1/2+δ)(2+|t|)^δ, where
P_N(t)=Σ_{1≤n≤N}μλ(n)exp(it log n). Set T=208(N+1).
The sharp finite Dirichlet-polynomial mean-value theorem gives
|∫_0^T|P_N(t)|²dt−T S_N|≤104 N S_N≤(T/2)S_N,
where S_N=Σ_{1≤n≤N}|μλ(n)|². On this finite interval, 2+|t|≤210(N+1),
so the integral is at most T C²210^(2δ)(N+1)^(1+4δ).
Divide by T/2. This proves the claim with 2C²210^(2δ), including N=0.
Only finite polynomials are integrated: no exchange of infinite-series limits,
no random twist and no exceptional physical orbit enter the argument.

**Quotient.** Put δ=ε/2 and use the reciprocal bound with δ. The classical
divisor estimate τ(n)≤Dδ n^δ and Cauchy–Schwarz give
|qλ(n)|²≤Dδ(N+1)^δ Σ_{d|n}|μλ(d)|² for 1≤n≤N.
Sum and use the exact convolution summatory identity:
Σ_{n≤N}Σ_{d|n}|μλ(d)|²=Σ_{m≤N}Σ_{d≤N/m}|μλ(d)|².
For m≤N, floor(N/m)+1≤2(N+1)/m. Thus the last sum is at most
Cδ 2^(1+δ)(N+1)^(1+δ) Σ_{m≥1}m^(-1-δ).
The last series converges because δ>0. Multiplying by the divisor bound
gives exponent 1+2δ=1+ε. N=0 has empty sum. Every premise is supplied by
full positivity or a proved unconditional finite-sum theorem.

This closes the exact candidate on paper. Lean verification remains separate.

## Cycle 6: strict reciprocal boundedness obstruction (paper)

Let hW be arbitrary full positivity and let G be its literal holomorphic
reciprocal on H={Re s>1/2}. The proved primitive representation is
G(s)=κ(s−1)exp(P(s)), κ≠0, P holomorphic on H. Thus G vanishes exactly at1.
Fix 1/2<x<1 and suppose |G|≤M on Re s>x. The far-right Dirichlet identity
and absolute convergence are already supplied by full positivity. The corpus's
bounded Dirichlet continuation theorem therefore makes G uniformly almost
periodic on every closed inner vertical strip.

Take r>0 with r<min((1−x)/2,1/2), and a closed inner strip containing
the closed disk centered at1 of radius r. On its boundary sphere G is nonzero;
compactness gives m=min|G|>0. Choose an m/3-almost period τ>2r+1.
Then |G(1+iτ)|<m/3, while |G(z+iτ)|>2m/3 on |z−1|=r.
The translated function is holomorphic on the disk. If it had no zero there,
its reciprocal would be holomorphic and the maximum-modulus principle would
give |G(1+iτ)|≥min_boundary|G(z+iτ)|, contradiction. Thus G(w)=0 for some
|w−(1+iτ)|<r. This w lies in H and has nonzero imaginary part, contradicting
the exact zero set {1}. Hence no such uniform M exists.

For each x>1, absolute convergence of the reciprocal Dirichlet series at some
a∈(1,x) supplies a uniform bound on Re s>x. Therefore its boundedness threshold
is exactly1. This statement makes no assertion at the endpoint x=1.
Absolute convergence at any a<1 would supply a bound on a strict inner
half-plane Re s>x with max(a,1/2)<x<1, impossible. Consequently the absolute
convergence threshold is also exactly1.

The parent recurrence fact is stated explicitly in Brevig–Kouroupis–Perfekt,
arXiv:2405.03522v2, Section3. Their boundary warning uses 1/ζ itself as an
example. Verdict: REDISCOVERED parent mechanism, BRIDGE source application;
not a new scientific claim. The exact full-positive unboundedness capstone is
now audited in Lean; the abscissa classification corollaries above remain paper
only. This does not retire the bounded-quotient route, because ζ cancels G's zero at1.

## Cycle 7: actual growth comparison (paper proof)

Fix arbitrary hW, 0<δ<1/2 and ε>0. Choose the literal global reciprocal G
from the existing primitive theorem. The already proved two-sided producer
Lindelöf theorem supplies, at every sufficiently large |t|, a local holomorphic
logarithm g on the disk centered at3+it of radius5/2−δ/4. This g equals the
literal log Dirichlet series on the disk's intersection with Re s>1, and
(|t|+3)^(-ε)≤|exp(g(σ+it))|≤(|t|+3)^ε for 1/2+δ≤σ≤5/2.

The disk lies inside Re s>1/2, contains these line points, and meets Re s>1
at its center. Analytic uniqueness therefore identifies G with exp(−g) on
the whole disk (`eqOn_exp_neg_of_agree`). Inverting the positive bounds gives
the same two-sided estimate for |G|. Multiplying by |ζ| gives

    (|t|+3)^(-ε)|ζ(σ+it)| ≤ |ζ(σ+it)G(σ+it)|
      ≤ (|t|+3)^ε|ζ(σ+it)|.

No division by ζ is used; this remains valid at its zeros. Threshold T may
depend on hW,δ,ε. The estimate is simultaneous for every indicated σ,t.
Apply it with ε/2 in both directions: a subpower upper bound for either ζ
or its actual quotient yields a subpower upper bound for the other on the
same inner strip. This proves the claimed growth equivalence on paper.
The comparison is a BRIDGE from a stronger existing source theorem, not a
new cancellation mechanism or a proof of either Lindelöf or bounded quotient.

## Cycle 10: actual reciprocal mean square (paper and Lean verified)

For every hW, choose the literal G already identified with its ordinary
Dirichlet series in cycle1. Write mu(n) for those coefficients. For every
real sigma>1/2 the following limit exists and is finite:

    lim_(T→infinity) (1/T) integral_0^T |G(sigma+it)|² dt
      = sum_(n≥1) |mu(n)|² n^(-2sigma).

Here T is real and positive. This is the actual function, with no random
twist or almost-everywhere selection. The result does not assert a uniform
bound in t or uniformity as sigma decreases to1/2.

Put delta=sigma−1/2>0. Choose 0<epsilon<delta/3. Cycle1 gives, for every
real t and u≥1,

    |A_t(u)| ≤ C (floor(u)+1)^(1/2+epsilon) (2+|t|)^epsilon,
    A_t(u)=sum_(1≤n≤u) mu(n)n^(-it).

Set a=1/2+epsilon<sigma. For u≥1 this is at most
C*2^a*u^a*(2+|t|)^epsilon. Finite summation by parts followed by the ordinary
series limit gives, for each integer N≥1,

    G(sigma+it) − sum_(n≤N) mu(n)n^(-sigma-it)
      = −A_t(N)N^(-sigma)
        + sigma*integral_N^infinity A_t(u)u^(-sigma-1)du.

The integral is absolutely convergent: its norm is bounded by a constant
times u^(a−sigma−1), whose exponent is less than−1. The endpoint at infinity
vanishes by the same bound. Thus the displayed identity entails

    |G(sigma+it)−P_N(t)|
      ≤ C*2^a*(1+sigma/(sigma−a))*(2+|t|)^epsilon*N^(a−sigma).

No factor |sigma+it| is introduced: the oscillation was included in A_t
before summation by parts, and the differentiated weight is the real power
u^(-sigma). This order of operations matters.

The coefficient energy S_sigma=sum_(n≥1)|mu(n)|²n^(-2sigma) is finite.
Indeed, cycle5 with 0<eta<2delta bounds the j-th dyadic block by a constant
times 2^(j*(1+eta−2sigma)); the geometric ratio is strictly less than1.

For T≥4 take N=floor(sqrt(T)). Then sqrt(T)/2≤N≤sqrt(T). The preceding
tail bound, uniformly for0≤t≤T, is O(T^((3epsilon−delta)/2)), hence tends to0.
Write e_T for this uniform error. The existing finite sharp mean-value theorem
applied to b_n=mu(n)n^(-sigma), 1≤n≤N, gives

    |(1/T)integral_0^T |P_N(t)|²dt − sum_(n≤N)|b_n|²|
      ≤ (104/T)sum_(n≤N)n|b_n|²
      ≤ 104*(N/T)*S_sigma.

Its right side tends to0, while the finite energy tends to S_sigma since
N tends to infinity. In particular these polynomial mean squares remain
bounded. Integral Cauchy–Schwarz and
||z+w|²−|z|²|≤2|z||w|+|w|² now bound the difference between the actual
and polynomial mean squares by

    2*e_T*sqrt((1/T)integral_0^T |P_N(t)|²dt) + e_T²,

which tends to0. This proves the exact limit without a Carlson theorem,
an infinite-polynomial mean-value interchange, or an unproved source bound.

The generic assertion using only ordinary convergence and H² is false by
Brevig–Kouroupis2026, Theorem6. Their Corollary2 supplies the order-zero
replacement. The proof above derives that replacement directly for this
source from already verified ingredients. Verdict: BRIDGE, not new scientific
novelty. The source mean identity is now formalized and directly audited in
`WeilWorkSingularArithmeticReciprocalMeanSquare.lean`. The bounded-product detector is
still open: a mean law does not control the exceptional orbit, and G itself
is provably unbounded on every half-plane crossing1.

### Uniform tail lemma used in the formalization

Fix alpha>1/2 and epsilon>0. Choose
eta=min((alpha-1/2)/2,epsilon)>0 and theta=1/2+eta<alpha.
For a_t(n)=mu(n)n^(-it), cycle1 and n+1<=2n give
|sum_(m<=n)a_t(m)|<=C*2^theta*(2+|t|)^eta*n^theta, n>=1.
Finite summation by parts with the real weight n^(-alpha) therefore bounds
every partial sum of the original series at alpha+it by

    K*(2+|t|)^eta,
    K=C*2^theta*(1+alpha*sum_(n>=1)n^(theta-alpha-1)).

The last sum is finite because theta<alpha. Inflate eta to epsilon using
2+|t|>=1. Apply the existing shifted uniform Abel tail estimate from
s0=alpha+it to s=sigma+it, sigma>alpha. The shift is positive real, so
1+|s-s0|/Re(s-s0)=2. This yields, simultaneously for all sigma>alpha,N,t,

    |G(sigma+it)-P_N(sigma+it)|
      <=4K*(2+|t|)^epsilon*(N+1)^(alpha-sigma).

The same literal G is used everywhere, identified by ordinary convergence.
This slightly weaker exponent than the single-Abel formula still proves
the mean law: take alpha=(sigma+1/2)/2 and epsilon<(sigma-alpha)/2.

An alternative final comparison avoids integral Cauchy–Schwarz. The N=0
tail bound gives |G|<=K(2+|t|)^epsilon. Since (N+1)^(alpha-sigma)<=1,
the same bound gives |P_N|<=2K(2+|t|)^epsilon. Consequently

    ||G|²-|P_N|²| <= 3K²(2+|t|)^(2epsilon)(N+1)^(alpha-sigma).

For N=floor(sqrt(T)) and epsilon<(sigma-alpha)/4, its supremum over
0<=t<=T tends to zero. Dividing the integral by T preserves that bound.
This also proves the same mean identity; it uses order zero twice rather
than a Cauchy–Schwarz estimate on the polynomial mean.

The formal proof uses alpha=(sigma+1/2)/2 and epsilon=(sigma-alpha)/8.
The strict inequality sqrt(T)<floor(sqrt(T))+1 gives the required negative
power comparison, including all real T sufficiently large. The four leaves
ReciprocalTail, SquareSummability, MeanComparison, and ReciprocalMeanSquare
passed targeted builds and final direct Lean audits. All six public capstones
use only propext, Classical.choice, and Quot.sound.

## Cycle 17: regular perturbations do not test the singular detector

This is a conditional diagnostic, not an example of a full-positive source
and not a new source capstone. Write Q_lambda(f) for the real full Weil
functional on the autocorrelation of a compact C2 test f. Suppose, only for
this diagnostic, Q_lambda(f)>=eta*integral |f|^2 for every such test, eta>0.
For w supported on n>=2 put B=2 sum |w(n)|/sqrt(n). Cauchy--Schwarz and
translation invariance give |autocorr_f(u)|<=integral |f|^2. The exact
arithmetic part of weilFullFunctional therefore gives

    |Q_(lambda+w)(f)-Q_lambda(f)| <= B*integral |f|^2.

Only finitely many arithmetic terms meet each compact autocorrelation.
Consequently B<eta/2 preserves a margin eta/2, hence full positivity.

Fix 0<a<1/2. Infinitely many primes and
p^(a-1/2)*log p -> 0 permit an increasing prime sequence p_j with
2*p_j^(a-1/2)*log p_j < eta*2^(-j-3), j>=0. Set
w(p_j)=sign(lambda(p_j))*p_j^a*log p_j, taking sign(0)=1, and w=0 elsewhere.
Then B<eta/2 and |lambda(p_j)+w(p_j)|>=p_j^a log p_j. The exact prime
Dirichlet-exponential identity gives |mu_(lambda+w)(p_j)|>=p_j^a.
Thus the universal reciprocal Ramanujan conjecture, if proved, would also
exclude every source with this uniform margin. Existence of such a margin
is unproved; this does not refute that conjecture.

In contrast, the exact WP03 target is invariant under this perturbation.
H(s)=-sum_(n>=2) w(n)/(log n)*n^(-s) converges normally on Re s>1/2 and
|H(s)|<=B/(2 log 2) there. On Re s>1 the literal reciprocals satisfy
G_(lambda+w)=G_lambda*exp(H); the identity theorem extends this identity
when both sources are full-positive. Both exp(H) and exp(-H) have norm at
most exp(B/(2 log 2)). Hence every inner-half-plane bound for zeta*G of
either source gives the corresponding bound for the other. This stability
argument is elementary Banach-algebra analysis (BRIDGE), not a solution.

## Cycle 20: forward coefficient critical square energy

Let lambda be any full-positive source, lambda0 its truncation below2, and
a_lambda=dirichletExp(logZetaCoeff(lambda0)). The claim is

    exists K>=0, forall N>=1,
      sum_(1<=n<=N) |a_lambda(n)|^2/n <= K*(1+log N).

No sign, multiplicativity, margin, or coefficient-size premise is added.
This claim concerns the forward series exp(L), not its reciprocal exp(-L).

First the exact logarithmic convolution identity is

    (log n)*a_lambda(n) = sum_(d*m=n) lambda0(d)*a_lambda(m), n>=1.

One justification uses only existing analytic parents: full positivity gives
absolute convergence of lambda0 and its log series on Re s>1; the Dirichlet
exponential theorem gives absolute convergence of a_lambda and L(a)=exp(L).
Differentiate on this open half-plane and use absolute Dirichlet convolution.
Both resulting series converge to the same function. Dirichlet uniqueness
identifies their coefficients for every n>=1. The n=1 terms are zero.

Take C>=0 from the existing multiplicative Toeplitz bound. At level N insert
c(m)=a_lambda(m)/sqrt(m) for 1<=m<=N, and c(m)=0 otherwise. Group the finite
double sum by k=n*m. Since lambda0 is real, its inner sum is the conjugate
of the logarithmic convolution identity. Thus exactly

    2*sum_(k<=N) (log k)*|a_lambda(k)|^2/k
       <= (log N+C)*sum_(k<=N) |a_lambda(k)|^2/k.                 (20.1)

There is no absolute-value replacement of the signed arithmetic convolution.
All excluded indices have zero cutoff or lambda0 value. This is the useful
orientation of the Toeplitz ceiling: using reciprocal coefficients instead
would put a minus sign on the nonnegative logarithmic energy.

For L>=0 define E(L)=sum_(1<=n<=exp L) |a_lambda(n)|^2/n and
F(L)=integral_0^L E(u) du. Finite summation on each compact interval gives
F(L)=sum_(n<=exp L) |a_lambda(n)|^2/n*(L-log n), including the term n=1.
Apply (20.1) at floor(exp L) and use log(floor(exp L))<=L to obtain

    (L-C)*E(L) <= 2*F(L).                                      (20.2)

F is locally absolutely continuous and F'=E almost everywhere. On L>C,
(F(L)/(L-C)^2)'<=0 almost everywhere, by (20.2). The fundamental theorem
for absolutely continuous functions makes this ratio nonincreasing. Fix
L0>C+1. Then F(L)<=F(L0)*(L-C)^2/(L0-C)^2 for L>=L0, and (20.2) gives
E(L)<=2*F(L0)*(L-C)/(L0-C)^2. The bounded initial interval is absorbed in K.
Taking L=log N proves the claim. The finite proof below is now formalized in
WeilWorkSingularArithmeticForwardCoefficients and passed its final direct audit.

For formalization the same step has a finite proof. Put
E_N=sum_(n<=N)w_n and H_N=sum_(n<=N)(log N-log n)*w_n, w_n=|a(n)|^2/n.
For N>=1, H_(N+1)=H_N+(log(N+1)-log N)*E_N. Choose N0 with log N0>C
and K0>=H_N0/(log N0-C)^2. If H_N<=K0*(log N-C)^2, then (20.1) gives
E_N<=2*K0*(log N-C). With d=log(N+1)-log N>=0, the exact recurrence gives
H_(N+1)<=K0*((log N-C)^2+2*d*(log N-C))<=K0*(log(N+1)-C)^2.
Induction proves both bounds for N>=N0; E_N<=E_N0 handles the finite head.
This version needs no integral or almost-everywhere differentiation.

The parent mechanisms are logarithmic differentiation, finite Toeplitz
testing, and Gronwall's inequality. Classification: BRIDGE until a stronger
scientific consequence survives the novelty audit. It neither bounds the
actual quotient nor removes exceptional heights. It does suggest an exact
stronger question: if r_lambda is the positive residue of exp(L) at1, does
sum_(n<=N)|a_lambda(n)-r_lambda|^2/n=o(log N)? That variance statement is
OPEN; (20.1) supplies an upper growth order, not its leading constant.

## Cycle24: exact two-prime composite compensation

This finite diagnostic concerns the real divisor-square matrix indexed by
(1,p,q,pq), not a full-positive source. Write a=lambda(p)/sqrt(p),
b=lambda(q)/sqrt(q), c=lambda(pq)/sqrt(pq). Its quadratic form is

    T_c(x)=2a(x0*xp+xq*xpq)+2b(x0*xq+xp*xpq)+2c*x0*xpq.

Let u=sqrt(a^2+b^2). The least possible upper quadratic-form budget over
all choices of c is exactly u. If u>0, its unique attaining choice is
c=-2ab/u. For this choice direct expansion gives

    u*(u*sum x_i^2-T_c(x))
      =(u*xp-a*x0-b*xpq)^2+(u*xq-b*x0-a*xpq)^2.

Hence the ceiling holds. The nonzero vector (u,a,b,0) has equality, so no
smaller budget works. Conversely, if budget u holds for every vector, insert
(u,a,b,t). The defect is u*t^2-2*(2ab+cu)*t. At
t=(2ab+cu)/u this is -(2ab+cu)^2/u, so positivity forces c=-2ab/u.
If u=0 then a=b=0, and vectors (1,0,0,1),(1,0,0,-1) force c=0.
The zero matrix then has budget0. These statements include every real a,b.

This is a classical Schur-complement completion calculation, classified
BRIDGE, with the exact signed composite coefficient as positive survivor.
It defeats the proposed local two-prime improvement of the star ceiling.
It does not supply consistent arithmetic coefficients on all integers,
all cutoffs, or the full Weil test space. Cycle23 is still open.
The exact square identity, ceiling classification and star equality are now
formalized in WeilWorkSingularArithmeticDivisorCompletion. Targeted build,
final direct check, and all three standard-axiom checks passed.

## Cycle25: retaining the product cutoff in prime-layer tests

The next candidate is genuinely coupled. Restrict the real multiplicative
matrix to prime singletons and squarefree products of two distinct primes.
All entries within each layer vanish; the cross-layer entry for singleton
p and pair pq is a_q=lambda(q)/sqrt(q). Thus the matrix is the symmetric
off-diagonal block with incidence map

    (R v)_(p,q)=a_q*v_p+a_p*v_q.

Arbitrary composite lambda values disappear because the root index1 is no
longer present. If every pair of k selected primes is retained, then

    R^T R=S*I+a*a^T-2*diag(a_p^2),   S=sum a_p^2.

For three nonzero entries, v_p=1/a_p gives
v^T(R^T R-SI)v=3>0. Hence this block has upper norm strictly exceeding
sqrt(S): the two-prime sharp repairs cannot persist at three primes.
For equal entries its squared norm is exactly (2k-2)*a^2. These are finite
paper calculations, not yet formalized source theorems or novelty claims.

The cutoff prevents an immediate source improvement. Retaining all pairs
of primes up to X requires level X^2 and Weil budget2log X+O(1). A gain
of at most sqrt(2) does not pay that cost. With the actual cutoff pq<=N,
the correct incidence map omits the other pairs. Testing v_p=a_p gives
the prospective exact source inequality

    4*sum_(p<q, pq<=N) (lambda(p)^2/p)*(lambda(q)^2/q)
      <= (log N+C)^2 * sum_(p<=N) lambda(p)^2/p.

The inequality follows from the norm of this restricted bipartite block;
its arithmetic reindexing and all finite support conditions still require
formal proof. It is not, by itself, the sharp prime-variance conjecture.
The research question is whether optimized nonuniform layer tests and the
full source compatibility improve that bound without losing the cutoff.

## Cycle27: all-cutoff Toeplitz sharpness

This proves a limitation of the complete family of logarithmic Toeplitz
ceilings, not a counterexample to full Weil positivity. Choose primes
p_0=2 and p_(j+1)>p_j^[2*(j+1)*(j+3)]. Euclid's theorem supplies each
choice. They increase strictly. Write L_j=log p_j and
b_j=((j+1)/(j+2))*L_j. Monotonicity gives sum_(i<j)L_i<=j*L_(j-1),
so 2*(j+2)*sum_(i<j)L_i<=L_j for j>=1; the j=0 case is empty.
In particular b_j>=0 and b_j+2*sum_(i<j)b_i<=L_j.
Define lambda(p_j)=sqrt(p_j)*b_j and lambda(n)=0 off this sequence.

Fix N>=1 and complex c supported in[1,N], with M=sum |c(m)|^2.
For every p>=2, the shift form
U_p=2 Re sum_m c(pm) conjugate(c(m)) is at most2M by AM-GM
and injectivity of m->pm. If N<p^2, retain only m with pm<=N.
Such m satisfy m<p, whereas pm>=p; the two index sets are disjoint.
AM-GM now gives U_p<=M. No sign of c or of a correlation is discarded.

Only finitely many selected primes occur below N. If none occur the form
is zero. Otherwise let p_j be the largest. When N<p_j^2, the entire form
is at most (b_j+2*sum_(i<j)b_i)*M<=L_j*M<=log(N)*M.
When N>=p_j^2, it is at most2*sum_(i<=j)b_i*M<=2*L_j*M<=log(N)*M.
Thus the exact multiplicative Toeplitz ceiling holds at every N with C=0.

At cutoff p_j, prime-square mass is at least lambda(p_j)^2/p_j=b_j^2.
Since p_j tends to infinity and (j+1)/(j+2) tends to1, every constant
theta<1 is exceeded by normalized prime-square mass at arbitrarily large
cutoffs. The star argument supplies the matching upper constant1 for this
relaxation. This rules out deriving cycle23 solely by more elaborate tests
inside the already extracted Toeplitz family, including cycle25 layers.
It leaves the full-positive conjecture open. The positive survivor is the
unconditional all-scale sparse construction and its exact sharp constant.

The matching upper square-mass bound also has a direct construction proof.
For the last selected prime p_j<=N, sum_(i<=j)b_i<=L_j<=log N and b_i>=0.
Consequently sum_(i<=j)b_i^2<=(sum_(i<=j)b_i)^2<=(log N)^2.
The empty-cutoff case is zero. Both bounds and the ceiling are now Lean
theorems in WeilWorkSingularArithmeticToeplitzSharpness. Its unconditional
capstone is exists_sharp_prime_supported_toeplitz_weight. This strengthens
the earlier finite calibration to one infinite witness and every cutoff.

## Cycle29 paper proof: sharp source summatory law

Status: dependency-closed paper argument, formalized and audited. This is a
classical Perron BRIDGE, not the uniform quotient detector.

Write lambda0(n)=lambda(n) for n>=2 and zero otherwise. The full-source
Herglotz theorem supplies Phi; R=A-Phi is holomorphic on Re s>1/2, and
L(lambda0,s)=1/(s-1)+R(s) on Re s>1. The already formalized regular-part
bound gives R(s)=O_delta(log(3+|Im s|)) uniformly for Re s>=1/2+delta.
Thus for every a>0, R(s)=O_delta,a((2+|Im s|)^a) there.

Fix epsilon>0, q=min(epsilon/4,1/4), a=q/2, c=1/2+q. For integer N>=1,
let w=smoothWeight N (1/2), with Mellin transform W. Its values on positive
integers are exactly 1 for n<=N and 0 otherwise. Absolute Dirichlet
convergence on Re s=2 gives

    2*pi * sum_(n<=N) lambda0(n)
      = integral_R [1/(1+it)+R(2+it)] W(2+it) dt.

For the pole contribution, 1/(s-1)=integral_1^infinity x^(-s) dx on Re s=2.
The double integral is absolutely integrable: its norm is
x^(-2)|W(2+it)|, the product of two integrable functions. Fubini followed
by Mellin inversion therefore identifies it with
2*pi*integral_1^infinity w(x) dx. This continuous main term lies between
N-1 and N-1/2, hence differs from N by a bounded constant.

Shift only R(s)W(s) to Re s=c. Holomorphy holds on the full closed strip;
rapid Mellin decay makes both vertical edges integrable and the horizontal
edges tend to zero. The fractional Mellin estimate with a<q bounds the
new vertical integral by O((N+1)^(c+q)). Since c+q<=1/2+epsilon, this proves

    |sum_(2<=n<=N) lambda(n)-N| <= C_epsilon (N+1)^(1/2+epsilon).

Every constant may depend on the source and epsilon, but not on N. No
nonnegativity, pointwise coefficient bound, local-mass bound, or slow-decrease
premise is used. In particular there is no smoothing error at the integers.

The centered coefficients lambda0(n)-1 consequently have an ordinary
Dirichlet series on Re s>1/2, by the existing polynomial Abel theorem.
At s=1, adding the harmonic-number asymptotic gives convergence of
sum lambda0(n)/n-log N. Subtracting the unconditional von Mangoldt
Mertens limit gives ordinary convergence of sum coneDeviation(lambda,n)/n.
This upgrades an existing local-mass-conditional conclusion; it does not
control total variation of the deviation or exceptional vertical heights.

The exact statements are `exists_sharp_source_sum_le`,
`centered_source_dirichletConvergesAt`, and
`exists_tendsto_coneDeviation_harmonic` in
`WeilWorkSingularArithmeticSummatory.lean`, supported by
`WeilWorkSingularArithmeticPolePerron.lean`. Both final direct Lean checks
passed; all five public declarations have only the standard three axioms.

## Cycle30 paper candidate: the harmonic limit is nonpositive

Status: second paper audit passed; formalization in progress, NOT formalized.
Do not cite C30 as a Lean theorem. Its target is the C29 harmonic limit's
sign, not the full WP03 detector. The following argument replaces the
three open obligations in the initial contour sketch; exact Lean dependency
assembly remains the next work. The second audit checked contour orientation,
pole cancellation, regularized Fubini and aggregate Gaussian error exponents.

Let Phi be the full-source Herglotz continuation, A the zeta archimedean
datum, R=A-Phi, and D=1/(s-1)+R. Let p(s)=(s-1)zeta(s), extended at1.
The corpus proves p entire, p(1)=1, p'(1)=gamma. Write

    ell = R(1)+gamma,
    a = lambda0*d_2 - (Lambda*d_2),
    V(s) = D(s)zeta(s)^2 + zeta'(s)zeta(s),
    F(s) = [D(s)zeta(s)+zeta'(s)]zeta(1-s).

Here ell is real. Ordinary Abel convergence at1, together with C29 and
the von Mangoldt Mertens constant, identifies ell with the ordinary limit
of sum coneDeviation(lambda,n)/n. On Re s>1, V=LSeries a. The coefficient
sequence is absolutely Dirichlet summable at every sigma>1, in particular
at9/8. This follows from the source's absolute convergence and the two
zeta factors; no pointwise Ramanujan bound is needed.

The exact algebra, away from1, is

    V(s) = p(s)[R(s)p(s)+p'(s)]/(s-1)^2,
    F(s) = [R(s)p(s)+p'(s)]zeta(1-s)/(s-1).

Thus V has at most a double pole with leading coefficient ell, and F has
at most a simple pole with residue -ell/2. Multiplication has removed
every possible zeta-zero pole. No zero-free assumption or RH enters.

### Positive boundary measure via a symmetric strip

Fix T>=1, g_T(s)=exp((s-1/2)^2/T^2),
b_T(s)=zeta(s)zeta(1-s)g_T(s), and c=3/4. On the closed strip
1/4<=Re s<=3/4, b_T is holomorphic, Gaussian-decaying in height, and
b_T(1-conj(s))=conj(b_T(s)). Also integral_R b_T(c+it)dt is real,
by Schwarz conjugation and t->-t.

For each real r, apply the residue theorem to
b_T(s)/(s-1/2-ir) across this symmetric strip. The left vertical integral
is minus the conjugate of the right one; the right-minus-left orientation
has residue +2*pi*b_T(1/2+ir). Therefore

    Re integral_R b_T(c+it)/(c-1/2+i(t-r)) dt
      = pi*b_T(1/2+ir).

The regularization -ir/(1+r^2) contributes a purely imaginary integral.
Insert the corpus's representation

    Phi(s) = integral [1/(s-1/2-ir)-ir/(1+r^2)] dmu(r) + iC.

Fubini is justified before separating the regularized terms: the existing
herglotzKernel bound is a polynomial in |t| times (1+r^2)^(-1), and
integral (1+r^2)^(-1)dmu is finite. Gaussian decay integrates the polynomial.
The imaginary constant contributes zero real part. Consequently

    Re integral_R Phi(c+it)b_T(c+it)dt
      = pi*integral |zeta(1/2+ir)|^2 exp(-r^2/T^2)dmu(r) >= 0.

This is a strip identity, not an assumption about pointwise boundary values.

Put B=A+1/(s-1). The function
[B(s)zeta(s)+zeta'(s)]zeta(1-s)g_T(s) is holomorphic on this strip.
Its real part on the critical line is zero: off zeta zeros it is
Re(xi'/xi)*|zeta|^2*g_T=0 by the functional equation; at zeros the
displayed product itself vanishes. Shift its integral from c to1/2.
It follows that Re integral_R F(c+it)g_T(c+it)dt <=0.
Shifting now from c to3/2 crosses only the simple pole at1, giving

    Re integral_R F(3/2+it)g_T(3/2+it)dt
      <= -pi*ell*exp(1/(4*T^2)).                         (30.1)

All horizontal edges vanish by the source regular-part logarithmic bound,
the corpus's polynomial zeta strip bounds, and Gaussian decay. Derivative
bounds follow from Cauchy's formula on slightly enlarged pole-free strips.

### Exact Gaussian extraction, with the source's actual premises

By the functional equation, F(s)=chi(1-s)V(s). Reflection t->-t and
g_T(1-s)=g_T(s) put the right-hand integral exactly into
ZetaLeftLineGaussianIntegrals.integral_zetaChi_mul_LSeries (r=1):

    integral_R F(3/2+it)g_T(3/2+it)dt = 2*pi*sum_n a(n)J_T(n).

ZetaChiGaussianKernel supplies BOTH

    |J_T(n)-2*exp(-4*pi^2*n^2/T^2)| <= C*(n/T^2+1/T),
    |J_T(n)| <= C*T^2/n^2.

The integer identity cos(2*pi*n)=1 is essential. Put sigma=9/8,
S=sum |a(n)|n^(-sigma)<infinity, and Y=T^(4/3). Below Y the summed
approximation error is bounded by

    C*S*[T^(-2)*Y^(sigma+1)+T^(-1)*Y^sigma]
      = O(S*T^(5/6)).

Above Y, use the quadratic bound for both the exact and Gaussian kernels:
the summed tail is O(S*T^2*Y^(sigma-2))=O(S*T^(5/6)). Hence

    sum a(n)J_T(n)
      = 2*sum a(n)exp(-4*pi^2*n^2/T^2) + O(T^(5/6)).   (30.2)

This needs neither local absolute mass nor individual coefficient bounds.
The published sharp-endpoint Gonek lemma is unnecessary.

### The remaining main term is exactly ell

Let X=T/(2*pi), M(s)=Gamma(s/2)/2, the Mellin transform of exp(-x^2).
Absolute Mellin inversion on Re s=3/2 gives

    sum a(n)exp(-(n/X)^2)
      = (1/(2*pi*i))*integral_(3/2) V(s)M(s)X^s ds.

Shift to3/4. The double-pole formula above gives

    sum a(n)exp(-(n/X)^2)
      = ell*M(1)*X*log X + C_lambda*X + O(X^(3/4)).     (30.3)

Here M(1)=sqrt(pi)/2>0. The shifted integral is absolutely integrable:
V has polynomial vertical growth on this line, while Gamma(s/2) has
exponential decay. The same bounds make the horizontal edges vanish.
Equations (30.2)-(30.3) imply that the left side of (30.1), divided by
T*log T, tends to sqrt(pi)*ell. Its right side tends to zero. Thus ell<=0.

Kill audit: all coefficients stay signed in V and its main term; absolute
values occur only in an error controlled by summability already derived
from hW. No off-line zero is crossed by a logarithmic derivative quotient.
No critical-line continuity of Phi is assumed. Reflection gives the
positive sign in the Cauchy identity; the pole of F has residue -ell/2.
For the canonical arithmetic sequence a=0 and ell=0, every displayed
identity reduces to zero. None of these steps yet constitutes a Lean audit.

### Cycle30 implementation refinement: regularized Fubini

For z=1/4+it, choose R=1+|t| in the existing Herglotz kernel bound.
Its coefficient is 6+6R+8R^2, bounded by 40(1+t^2). Hence

    |K(1/4+it,r) v(t)|
      <= 40*C / ((1+t^2)(1+r^2))

whenever |v(t)|(1+t^2)^2<=C. The right side is integrable for Lebesgue
measure in t and the source boundary measure in r. This proves joint
integrability before interchanging integrals. For each fixed r, the
Cauchy quotient is integrable since its denominator norm is >=1/4;
only then is its regularizing term separated in the t-integral.
Conjugation under t -> -t makes the test integral real, cancelling both
the kernel correction and the purely imaginary continuation constant.

For the actual zeta-Gaussian test, polynomial bounds on the high part of
the quarter strip are completed by compactness on the low part. The
existing Gaussian moment bound absorbs four extra powers, yielding
uniform fourth-order decay. The exact source integral is absolutely
integrable; its nonnegativity is not an artifact of the default value
assigned to a nonintegrable Bochner integral.

Formal implementation: CauchyReflection, HerglotzPairing and GaussianPairing
leaves under the `WeilWorkSingularArithmetic` prefix. All three targeted
builds and final direct checks passed; five axiom audits are standard-only.
This completes the pairing sub-obligation, not the full C30 sign argument.

### Cycle30b implementation refinement: canonical subtraction and pole transport

The canonical datum obeys A(s)+1/(s-1)=O(1+|Im s|) on the quarter strip.
Together with the corpus polynomial bounds for zeta and its derivative,
this bounds J before Gaussian weighting. Compactness fills the bounded
height region; Gaussian moments give integrable inverse-square decay.
The corpus critical-line identity includes zeta zeros, so J has purely
imaginary value there without any division by zeta. Contour transport
from1/2 to3/4 proves its real integral is zero. Subtracting the C30a
identity yields the exact equality

    Re integral_(3/4) F(s)g_T(s) dt
      = -pi * integral |zeta(1/2+ir)|^2 exp(-r^2/T^2) dmu(r).

Define P(s)=R(s)p(s)+p'(s). It is holomorphic on Re s>1/2, including
at1 and at zeta zeros. The algebraic identities F=P*zeta(1-s)/(s-1)
and V=p*P/(s-1)^2 give P(1)=ell, residue(F,1)=-ell/2 and the leading
double-pole coefficient of V equal to ell.

For the actual continuation Phi, the corpus Harnack estimate directly
bounds R=A-Phi on Re s>=3/4 by C log(|Im s|+3)+C. On the strip from3/4
to3/2, the high-height pole term is bounded. Polynomial zeta and zeta'
bounds therefore give polynomial growth for F; Gaussian moments again
give inverse-square decay. The simple-pole vertical shift applies and
preserves the exact equality

    Re integral_(3/2) F(s)g_T(s) dt
      = -pi * Re(P(1)) * exp(1/(4*T^2))
        -pi * integral |zeta(1/2+ir)|^2 exp(-r^2/T^2) dmu(r).

No reality claim about P(1) is needed for this real-part identity. The
later identification with the ordinary real harmonic limit supplies it.
The canonical subtraction, pole numerator and contour transport are now
formally audited. The arithmetic extraction below is also audited; the
one-sided Mellin sign remains to be formalized.

For coefficient extraction use the literal complex sequence
a=((lambda0-Lambda)*1)*1. Full positivity gives absolute convergence of
lambda0 for every real exponent>1. The von Mangoldt and constant-one
series converge absolutely there too, so the convolution theorem gives
L(a,s)=V(s), with no pointwise coefficient estimate. For s=3/2-it, put
w=1-s=-1/2+it. The corpus functional equation gives F(s)=chi(w)V(s)
and g_T(1-w)=g_T(w). Reflection t->-t and the generic chi transform
therefore identify the actual right contour with 2*pi*sum a(n)J_T(n).
The coefficient at zero vanishes by the convolution definition. This
preserves the signed sequence throughout the exact identity.

The aggregate kernel bound can avoid introducing finite partial sums:
for every integer n>=1, split at Y=T^(4/3). In the near range, multiply
the pointwise approximation by n^(9/8); its two terms are bounded by
T^(5/6) and T^(1/2), respectively. In the far range, both kernels give
T^2*n^(-7/8)<=T^(5/6). Thus one uniform pointwise bound for
n^(9/8)*|J_T(n)-2*exp(-4*pi^2*n^2/T^2)| can be multiplied by the
summable majorant |a(n)|/n^(9/8) and summed. This also verifies
summability before subtracting the two infinite series.

### Cycle30c candidate refinement: one-sided Mellin bound instead of an asymptotic

The full double-pole Mellin contour shift is stronger than the sign target
requires. Let H(x)=sum a(n)exp(-(n*x)^2), x>0. The exact signed contour
identity, its nonpositive spectral term and the aggregate kernel error
give Re H(x)<=C*x^(-5/6) for0<x<=1, after enlarging C to absorb the
bounded pole term and the fixed Gaussian scaling. The source pole value
is fixed, so its sign need not be known for this upper estimate.
For x>=1, exp(-(n*x)^2)<=1/(n*x)^2 and absolute summability at2 give
|H(x)|<=S2*x^(-2). The n=0 coefficient is zero.

For1<sigma<3/2, absolute summability at sigma justifies Fubini:

    integral_0^infinity x^(sigma-1) H(x) dx
      = Gamma(sigma/2)/2 * V(sigma).

Indeed each absolute term integrates to
|a(n)|*n^(-sigma)*Gamma(sigma/2)/2; its sum is finite. Taking real
parts and applying only the upper bound on H gives

    Gamma(sigma/2)/2 * Re V(sigma)
      <= C/(sigma-5/6) + S2/(2-sigma) <= 6*C + 2*S2.

The real Gamma factor is positive and continuous at1/2. Multiply by
(sigma-1)^2 and let sigma decrease to1. The verified candidate pole
identity gives the left limit sqrt(pi)/2*Re P(1); the right tends to0.
Consequently Re P(1)<=0. Identifying P(1) with the ordinary real harmonic
limit still gives the same C30 conclusion.

Kill audit: this uses an upper bound, not an absolute bound, on H near0.
It excludes a positive double-pole coefficient and permits a negative
one. It does not invoke Mellin holomorphy across1, assume positivity of
the signed coefficients, or infer vanishing of the pole. The corpus
MellinPoleRadialGrowth no-go concerns absolute growth and cannot directly
replace this one-sided argument. Verdict BRIDGE, paper refinement under
corpus audit; no new Lean conclusion is claimed here.

The next assembly must establish convergence of both extracted series,
not only their difference. Absolute Dirichlet summability at2 and
gaussW(T,n)<=T^2/n^2 prove absolute convergence of sum a(n)gaussW(T,n).
Adding twice this series to the already absolutely convergent error
series proves convergence of sum a(n)J_T(n). Thus linearity gives

    2*Re sum a(n)gaussW(T,n)
      = Re sum a(n)J_T(n) - Re sum a(n)(J_T(n)-2*gaussW(T,n)).

The exact contour bound controls the first term by
|Re P(1)|*exp(1/4)/2 for T>=1; the error norm controls the second by
C*T^(5/6). Absorb the fixed pole bound using1<=T^(5/6). This pays the
signed Gaussian upper bound with the actual source, before any Mellin
comparison. The subsequent Mellin argument must retain a separate proof
of absolute integrability; an identity between default-valued integrals
alone would not suffice for the one-sided comparison.

For the Lean implementation, use Hpi(t)=sum a(n)exp(-pi*n^2*t).
Its exact transform is Mellin(Hpi,sigma/2)=Gamma_R(sigma)*V(sigma),
directly matching mathlib hasSum_mellin_pi_mul_sq. The Gaussian parameter
T=sqrt(4*pi/t) yields Re Hpi(t)<=C*t^(-5/12) on0<t<=1 and
|Hpi(t)|<=S/t on t>=1. For1<sigma<3/2 the two real Mellin integrals are
bounded above by12*C and4*S. The known identity Gamma_R(1)=1 and
continuity at1 identify the rescaled limit directly with Re P(1).
No separate positivity assertion about Gamma_R away from1 is needed.
Continuity at1 follows, for example, by inverting the globally
differentiable reciprocal Gamma_R and using its nonzero value at1.

The uniform comparison need not evaluate parameter-dependent integrals.
For0<t<=1, t^(sigma/2-1)*Re Hpi(t)<=C*t^(-11/12); for t>=1 the
same integrand is <=S*t^(-5/4), whenever1<sigma<3/2. These fixed powers
are integrable on the respective intervals. Their piecewise sum therefore
gives a uniform finite upper bound for the real Mellin integral. This
upper envelope is not an absolute-value majorant; actual Mellin
integrability must still be supplied independently by absolute Dirichlet
summability and the termwise Gamma norm integrals.

The following integrability step was checked in a minimal mathlib scratch
with `lake env lean` (exit0, no diagnostics). It is preserved here for the
actual-source Mellin implementation; it is not itself a new source
conclusion. Both summand integrability and the weighted norm sum still
have to be instantiated for a(n)exp(-pi*n^2*t).

```lean
open Complex MeasureTheory Set Filter Topology

example {μ : Measure ℝ} {f : ℕ → ℝ → ℂ}
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable fun n => ∫ t, ‖f n t‖ ∂μ) :
    Integrable (fun t => ∑' n, f n t) μ := by
  refine ⟨(AEMeasurable.tsum fun n =>
    (hf n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    (∫⁻ t, ‖∑' n, f n t‖ₑ ∂μ) ≤ ∫⁻ t, ∑' n, ‖f n t‖ₑ ∂μ :=
      lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ t, ‖f n t‖ₑ ∂μ :=
      lintegral_tsum fun n => (hf n).aestronglyMeasurable.enorm
    _ = ∑' n, ENNReal.ofReal (∫ t, ‖f n t‖ ∂μ) :=
      tsum_congr fun n =>
        (ofReal_integral_norm_eq_lintegral_enorm (hf n)).symm
    _ < (⊤ : ENNReal) := hs.tsum_ofReal_lt_top
```

The norm-integral calculation to instantiate this is already present in
mathlib NumberTheory/LSeries/MellinEqDirichlet.lean, in the proof of
hasSum_mellin: GammaIntegral_convergent gives the scaled individual
integrals, and its norm calculation gives the summable majorant.
The exact pi-square transform is hasSum_mellin_pi_mul_sq. The present
six-leaf source result supplies all arithmetic summability and Gaussian
envelopes, but this final Mellin instantiation is still unformalized.

### C30d harmonic identification and remaining frontier

Let b(k)=lambda0(k+1)-1. C29 proves ordinary convergence of its Dirichlet
series on Re s>1/2. The corpus uniform Abel theorem makes its sum
holomorphic there, hence continuous at1. On Re s>1 absolute convergence
and the source identity identify this sum with

    R(s) - (zeta(s)-1/(s-1)).

The existing zeta Laurent limit is gamma. Therefore the ordinary centered
harmonic sum has complex value R(1)-gamma. Adding the usual harmonic
constant gamma and subtracting the von Mangoldt harmonic constant -gamma
gives the deviation limit R(1)+gamma=P(1). Every interchange here is paid
either by absolute convergence to the right of1 or ordinary convergence
at1 plus continuity from an already convergent half-plane.

The old WeilConeHarmonicPinning.nonpos_of_tendsto_harmonicSum additionally
requires NotchSmall. C30's exact target removes that premise. Its scalar
sign still does not prove zero, positivity of coefficients, absolute
harmonic summability, the signs of all twisted fibres, or WP03's uniform
quotient bound. Those remain distinct gates. The next conjectures must
address localization/twisting or directly bound the quotient, not promote
the scalar inequality to rigidity without proof.

### C31 preliminary successor: polynomial weights and the scalar face — FAILED

2026-10-08 kill audit: the phase-free arithmetic profile and Mellin
multiplier below are FALSE AS STATED. The kernel approximation is
J_T(y)=2 W_T(y) cos(2*pi*y)+error, not 2 W_T(y)+error.
C30 uses integer y, where the cosine is exactly one. At y=n/2 the
factor is (-1)^n. The historical candidate below is retained to expose
the failed step; none of its harmonic-equality conclusions is established.

This is a conjecture under audit, not an established consequence. For a
real finite Dirichlet polynomial Q(s)=sum_m c_m m^(-s), multiply the source
test by q(s)=Q(s)Q(1-s). The critical-line value is |Q(s)|²; q is symmetric
under s->1-s and bounded on every closed vertical strip. Thus the
canonical reflection and positive spectral pairing should persist.

The exact corpus kernel transform includes a factor r:

    integral chi(w)L(a,1-w) r^w g_T(w) dt
      = 2*pi*r*sum_n a(n)J_T(n*r).

Since q(s)=sum_(m,k) c_m*c_k/m * (m/k)^(1-s), its arithmetic Gaussian
profile is sum_(m,k) c_m*c_k/k * Hpi((m/k)^2*t). Its Mellin transform is
Gamma_R(s)*V(s)*Q(s)*Q(1-s), with no missing scale factor. Proving the
same O(T^(5/6)) aggregate error at each fixed positive scale would give
RePsource(1)*Q(1)*Q(0)<=0. For Q(s)=1-c*2^(-s), 1<c<2 gives Q(1)Q(0)<0;
together with C30 this would force RePsource(1)=0.

Kill gates: prove actual convergence for the finite dilates; extend the
kernel error to all positive real frequencies rather than assert scaling
of J; transport the exact weighted contour and its residue; keep the
spectral term's sign; prove the literal Mellin factor. Harmonic equality
is not the riemannKernelAutocorr equality in the existing exposed-point
theorem. No rigidity conclusion follows from that name alone. This
candidate is not yet Lean code, nor a dependency-closed formal result.

The first concrete test need only use Q(s)=1-(3/2)*2^(-s). Its profile is

    Hq(t)=(17/8)*Hpi(t)-(3/4)*Hpi(t/4)-(3/2)*Hpi(4*t),

and its Mellin multiplier is

    q(s)=17/8-(3/4)*2^s-(3/2)*2^(-s),  q(1)=-1/8.

The negative coefficients mean C30's separate upper bounds cannot be
combined to prove an upper bound for Hq. The new positive boundary
pairing with |Q|² is essential; using only existing scalar inequalities
would be circular. This explicit three-dilate test is the smaller first
formal target if the weighted contour audit succeeds.

C30d formal status: GaussianProfile, Mellin, MellinBound, PoleSign and
HarmonicSign now formalize the full C30 paper chain above. All five
targeted and final direct checks pass; all12 public axiom lists are
standard-only. In particular the actual Mellin integrability obligation,
pole sign and ordinary harmonic identification are closed. The phase-free
C31 successor failed the arithmetic kill audit; WP03 remains open.

### C31a positive survivor: exact scaled arithmetic extraction

Write a(n)=sourceSquareCoeff(lam)(n), W_T(y)=exp(-4*pi^2*y^2/T^2),
and J_T(y)=leftKernel(T,y). The already-proved pointwise kernel estimate
is |J_T(y)-2 W_T(y) cos(2*pi*y)| <= A(y/T^2+1/T) for y>=0,T>=1.
The square-tail estimates give |J_T(y)|<=B*T^2/y^2 and
W_T(y)<=T^2/y^2 for y>0. With |cos|<=1 and Y=T^(4/3), splitting
0<y<=Y and y>Y proves, uniformly for ALL positive real y,

    y^(9/8) |J_T(y)-2 W_T(y) cos(2*pi*y)| <= C*T^(5/6).

Indeed the near terms are A(T^(5/6)+T^(1/2)); the far term is
(B+2)T^2 Y^(-7/8)=(B+2)T^(5/6). Full positivity already supplies
S=sum |a(n)|/n^(9/8)<infinity, with a(0)=0. Substitution y=n*r,
r>0, gives absolute summability of the actual source error and

    norm(sum a(n)[J_T(n*r)-2W_T(n*r)cos(2*pi*n*r)])
      <= C*S/r^(9/8)*T^(5/6).

Both main series are absolutely summable separately: use the square-tail
bounds above and sum |a(n)|/n^2<infinity. Thus sum subtraction is valid.
The existing exact chi-transform, the zeta functional equation, and
t->-t give the literal source contour identity

    integral F(3/2+it)*r^(1-(3/2+it))*g_T(3/2+it) dt
       =2*pi*r*sum a(n)J_T(n*r).

Consequently its difference from
4*pi*r*sum a(n)W_T(n*r)cos(2*pi*n*r) is O_r(T^(5/6)).
The stronger quantifier order exposed by this proof is also valid:
one constant K=2*pi*C*S works for EVERY r>0, with error
K*r^(-1/8)*T^(5/6). This follows exactly from
r/r^(9/8)=r^(-1/8); no scale-dependent source constant is needed.
For a reduced rational r=m/k the cost is (k/m)^(1/8).
This uniform refinement is a BRIDGE, not literature-novel arithmetic
rigidity; it retains information needed for growing denominator families.
This is a dependency-closed paper proof of the positive survivor.
Formal status: COMPLETE for C31a. TwistedGaussianError and
TwistedExtraction prove all these statements, including the uniform
quantifier order, contour integrability and half-scale parity identity.
Both targeted and final direct Lean checks pass; all nine public axiom
audits are standard-only. No smallness, sign, or twisted pole-limit
premise has been added. It is a BRIDGE, not uniform quotient control.

The corrected polynomial profile for Q(s)=1-c*2^(-s) is

    (1+c^2/2)H(t) -(c/2)H_alt(t/4) -c H(4t),
    H_alt(t)=sum a(n)(-1)^n exp(-pi*n^2*t).

Its Mellin transform contains the distinct additive twist V_alt(s).
It does not factor as Gamma_R(s)V(s)Q(s)Q(1-s). The new research
question is whether positivity constrains the actual additive-twist
residues strongly enough to control WP03's quotient. Weighted positivity
is now paid by C31b. Twisted residue limits remain unpaid.

### C31b completed: the actual two-term polynomial inequality

For each real c and hW, the exact target is existence of C>=0 with

    Re[(1+c^2/2)H(t) -(c/2)H_alt(t/4) -cH(4t)] <= C*t^(-5/12)

for 0<t<=1. This assertion has no NotchSmall, local-mass, convergence
at the pole, or sign assumption on the deviation. It is a BRIDGE to
the stronger conjecture that the full fibre Bochner law can be obtained
from hW alone. Twisted pole convergence is a separate open core of that
stronger conjecture, not a premise of the present Gaussian inequality.

Paper proof of the displayed Gaussian bound: put Q(s)=1-c*2^(-s),
q(s)=Q(s)Q(1-s). This entire function is bounded on every closed
vertical strip, obeys q(1-s)=q(s) and q(conj(s))=conj(q(s)), and has
q(1/2+iu)=|Q(1/2+iu)|^2>=0. Multiply the C30 canonical pairing by q.
Its existing quarter-strip inverse-square decay persists. Vertical
shift to Re=1/2 shows that its real integral is zero, because the
canonical pairing there is purely imaginary and both q and g_T are
real. The actual Herglotz pairing theorem applies to zeta(s)zeta(1-s)
g_T(s)q(s): holomorphy and both reflection laws hold, and multiplication
by the strip bound for q preserves its existing fourth-order decay.
It gives a nonnegative real Phi pairing and hence a nonpositive real
source pairing on Re=3/4. All these integrals converge absolutely by
the same decay and weighted boundary-measure Fubini theorem as C30.

On 3/4<=Re s<=3/2, the source's existing tail decay also persists
after multiplication by q. Its sole pole has residue
-P(1)q(1)g_T(1)/2. The residue shift therefore bounds the real
right-line integral by -pi*Re(P(1))*q(1)*exp(1/(4T^2)), uniformly
bounded above for T>=1. No value or sign of q(1) is assumed.

The exact expansion, in the normalization of C31a, is

    q(s)=1+c^2/2 -(c/2)*2^(1-s) -c*(1/2)^(1-s).

C31a extracts the three source contours, with scale factors 1,2,1/2.
After division by 4*pi their combined Gaussian term is
(1+c^2/2)S_T(1)-c*S_T(2)-(c/2)*S_T(1/2), where
S_T(r)=sum a(n)W_T(nr)cos(2*pi*nr). The absolute error is
O_c(T^(5/6)) by the three C31a norm bounds. Integer cosine identities
give S_T(1)=H(t), S_T(2)=H(4t), S_T(1/2)=H_alt(t/4),
where t=4*pi/T^2. The compact remaining T interval when 0<t<=1
is already within T>=1. This proves the displayed bound on paper.
Lean formalization COMPLETE: PolynomialWeight, PolynomialPairing,
PolynomialShift, PolynomialGaussian and PolynomialProfile prove the
actual statements. Final targeted/direct checks pass without warnings;
all30 public axiom reports are standard-only. The final profile theorem
is exists_re_sourceTwoPointGaussianProfile_le.

SOTA audit: rational additive twists are classical (e.g. Fazzari,
https://arxiv.org/abs/2306.15553). Gcd Gram factorization and totient
diagonalization are also classical (Guillot--Wu,
https://arxiv.org/html/1901.01947v1, introduction). The internal
WeilConeNotchBochnerLaw requires NotchSmall and all gcd-sum limits;
GcdWeightedSeriesInversion pays the sieve limit using an absolute tail.
Neither is available for this arbitrary source. Any novelty claim must
concern removal of those analytic assumptions, not these representations.

### C32a candidate: actual parity pole compactness, without a pole premise

Let V_alt(s)=sum a(n)(-1)^n/n^s on Re s>1. This converges absolutely
by the actual source coefficient theorem. Write ell=Re(P(1))<=0 and

    a_sigma=(sigma-1)^2 Re(Gamma_R(sigma)V(sigma)),
    b_sigma=(sigma-1)^2 Re(Gamma_R(sigma)V_alt(sigma)).

The corpus's ordinary-pole theorem gives a_sigma -> ell. No limit for
b_sigma is assumed. The next precise conjecture is the unconditional
asymptotic interval bound

    dist(b_sigma, [-ell/2+sqrt(2)*ell, -ell/2-sqrt(2)*ell]) -> 0

as sigma decreases to1. In particular b_sigma is bounded near1. This
is weaker than convergence, and neither convergence nor ell=0 is claimed.
The parent C32 conjecture remains the actual full arithmetic fibre law;
this interval assertion is its first analytic step, not a replacement
for C32 or WP03.

Dependency-closed paper argument from C31b: the alternating Gaussian
series is absolutely Mellin integrable for Re s>1 by the same norm
series as the untwisted source. Its exact Mellin transform is
Gamma_R(s)V_alt(s). Changing t to t/4 and4t in those actual integrals
then gives the weighted transform

    Gamma_R(s)[(1+c^2/2-c*2^(-s))V(s)
                 -(c/2)*2^s V_alt(s)].

The small-t bound of C31b and the actual norm tail O_c(1/t) give a
fixed integrable real upper envelope on1<sigma<3/2, exactly as in C30d:
C_c*t^(-11/12) below1 and D_c*t^(-5/4) above1. The tail norm bound
follows from the all-T twisted Gaussian bound at scale1/2, not from
a signed upper estimate. Thus the real transform is at most B_c,
independent of sigma. Multiplying by(sigma-1)^2 yields

    (1+c^2/2-c*2^(-sigma))*a_sigma
      -(c/2)*2^sigma*b_sigma <= (sigma-1)^2 B_c.

Take the TWO FIXED coefficients c=+sqrt(2) and c=-sqrt(2).
Their nonzero b_sigma coefficients tend to minus/plus sqrt(2).
Dividing each inequality by its positive absolute coefficient and
using a_sigma->ell gives respectively

    liminf b_sigma >= (sqrt(2)-1/2)*ell,
    limsup b_sigma <= (-sqrt(2)-1/2)*ell.

These statements mean the corresponding eventual epsilon bounds;
they do not presuppose a finite liminf/limsup or any cluster point.
Together they prove the displayed interval assertion and boundedness.
Every cluster value beta therefore satisfies
(beta+ell/2)^2<=2*ell^2. When ell=0 the interval collapses and the
normalized parity expression tends to0; for ell<0 this argument leaves
a nontrivial interval. Sharpness here refers only to the two-term
quadratic constraint: every beta in this interval satisfies
ell*c^2/2-(ell/2+beta)*c+ell<=0 for every real c.

Kill audit: no phase-free factorization, no asserted parity Laurent
expansion, no extraction of an ordinary subseries limit from ordinary
convergence, and no coefficient sign. The endpoint bound is a BRIDGE;
its usefulness is replacing an assumed twisted pole by an actual
asymptotic constraint. Lean status: OPEN. The first implementation debt
is actual alternating Mellin convergence and the exact weighted identity.

The quadratic inequalities alone cannot establish parity convergence
when ell<0: any real-valued function b_sigma lying in the displayed
nontrivial interval satisfies all their limiting quadratic constraints,
including functions without a limit. This is a logical obstruction to
that deduction, not a full-positive arithmetic counterexample. A proof
of ordinary arithmetic-limit existence must exploit additional source
structure; finite-dimensional discriminant algebra cannot supply it.
