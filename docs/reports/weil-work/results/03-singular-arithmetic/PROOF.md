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
not a new scientific claim. The positive source classification above is paper
only until the exact full-positive theorem is checked in Lean. It does not
retire the bounded-quotient route, because ζ cancels G's zero at1.

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
