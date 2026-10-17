# Distant-copy amplitude classification and polar continuity

## Domain and notation [PAPER PROOF]

Let f be an actual compact C² real source with R=h_f(0)>0. Choose D>0 with
h_f(x)=0 whenever |x|>D. Write H=h_f/R, E=J/R, and

    g_(a,T)(u)=f(u)-a f(u-T),  b(a)=a/(1+a²),  T>D.

All copies are actual compact C² sources, smooth when f is smooth. Their masses
are (1+a²)R>0. The existing exact correlation expansion gives

    H_g(x)-H(x)=-b(a)(H(x-T)+H(x+T)).

The square (|a|-1)²>=0 proves |b(a)|<=1/2. No grid value is assumed zero or
nonnegative. The short-support witnesses below derive their grid properties.

## 1. Exact global correlation error [PAPER PROOF]

For T>D, H(x-T) and H(x+T) cannot both be nonzero: otherwise both shifted
arguments have absolute value at most D, and their difference 2T would be at
most 2D. Since |H|<=1, their sum has absolute value at most one. Consequently

    |H_g(x)-H(x)|<=|b(a)| for every x.

At x=T, H(T)=H(2T)=0 and H(0)=1, so H_g(T)=-b(a). The upper bound is attained:

    ||H_g-H||_infinity=|b(a)|.

Thus, for arbitrary separated parameters T_n>D, global uniform convergence
H_gn->H holds if and only if b(a_n)->0. The reverse implication to b->0 tests
the uniform error at the moving location x=T_n; it requires no fixed-point
interchange. If T_n->infinity, the older local-copy identity also gives exact
agreement with H eventually on each fixed bounded window, for every amplitude.

## 2. Uniform energy control and energy convergence [PAPER PROOF]

Assume T>=D+1 and put A_f=integral_R |h_f(x)| dx, which is finite and nonnegative.
The already certified translated-packet identity and envelope imply

    |E(g_(a,T))-E(f)| <= F_D(T) A_f/(2R),
    F_D(T)=2 exp(-(T-D)/2)/(1-exp(-2)).

Indeed the exact difference is b(a)/R times integral_(0,infinity)
h_f(x-T) w(x) dx, whose absolute value is at most F_D(T) A_f. The coefficient
bound |b|<=1/2 yields the estimate. F_D is positive and decreasing. Therefore
all parameters with T>=D+1 have the single ceiling

    K=E(f)+F_D(D+1) A_f/(2R).

This also bounds the seed, and K>=0. If T_n->infinity, the error bound tends
to zero independently of the amplitudes. Hence E(g_n)->E(f) for arbitrary a_n.

## 3. Exact compactness criterion for escaping copies [PAPER PROOF]

Let T_n>=D+1 tend to infinity. The copies belong to the actual source class at
the common ceiling K above. Their normalized correlations have compact closure
in the global supremum norm if and only if b(a_n)->0.

If b(a_n)->0, section 1 gives global uniform convergence to H. The range of a
convergent sequence together with its limit is compact; its closed subset given
by the closure of the range is compact.

Conversely, compact closure gives uniform continuum tails by the signed-grid
criterion. Given epsilon>0, choose its common tail radius. Eventually T_n lies
beyond that radius, so |b(a_n)|=|H_gn(T_n)|<epsilon. This proves b(a_n)->0.
Combining with the signed-grid criterion also characterizes uniform signed trace
decay by this same exact scalar condition.

## 4. Polar moment law and its exact continuity scale [PAPER PROOF]

Define the normalized polar moment by the actual finite integral

    P(f)=(1/R_f) integral_(0,infinity) h_f(x) cosh(x/2) dx.

Evenness and the existing exponential-moment product identity give

    2 integral_(0,infinity) h_f(x) cosh(x/2) dx = M_+(f) M_-(f),
    M_+(f)=integral f(u) exp(u/2) du,
    M_-(f)=integral f(u) exp(-u/2) du.

Compact support discharges all integrability requirements. The exact source
moment multipliers are M_±(g)=(1-a exp(±T/2))M_±(f). Their product multiplier is

    (1-a exp(T/2))(1-a exp(-T/2))=1+a²-2a cosh(T/2).

Dividing by the actual mass (1+a²)R proves

    P(g)=(1-2b(a)cosh(T/2))P(f).

If P(f) is nonzero, P(g_n)->P(f) if and only if b(a_n)cosh(T_n/2)->0.
The forward implication follows by solving exactly for the weighted coefficient:
b(a_n)cosh(T_n/2)=(P(f)-P(g_n))/(2P(f)); the reverse is continuity of scalar
arithmetic. If P(f)=0, every copy also has zero polar moment. This classification
is stronger than a bare failure of polar closedness: it identifies the exact
additional control for this family.

## 5. Actual smooth witnesses and sharpness [PAPER PROOF]

For any r>0, take the concrete smooth bump p centered at zero with inner radius
r/2 and outer radius r. It is nonnegative, compactly supported, and p(0)=1.
The integral of p² and both exponential moments are strictly positive, because
each continuous nonnegative integrand is positive at zero. Thus R_p>0 and P(p)>0.
Its correlation vanishes outside radius D=2r.

Choose r=log(2)/4, so D=log(2)/2<log(2), and T_n=D+2+n. The preceding construction
gives one energy ceiling K for every amplitude choice.

**Pointwise grid blindness does not imply compactness.** Take a_n=1. Then b=1/2,
E(g_n)->E(p), and H_gn(T_n)=-1/2, so the correlations are not relatively compact.
For every fixed grid node log m, m>=2, H_p(log m)=0 by support. Eventually
T_n>D+|log m|, so exact local preservation gives H_gn(log m)=0. The positive
survivor is the exact uniform-trace/amplitude criterion of section 3; pointwise
eventual zeros cannot replace its uniform quantifiers.

**Polar balance is not closed under global correlation and energy convergence.**
Take a_n=exp(-T_n/2). The actual source is the existing polarCopy(p,T_n), so its
polar moment is exactly zero. The amplitudes, hence b(a_n), tend to zero. Thus
H_gn converges globally uniformly to H_p and E(g_n)->E(p), while P(p)>0.
The correlation family has compact closure and uniform signed-grid trace decay,
by section 3 and the signed-grid criterion. Nevertheless its polar limit fails
balance. Section 4 supplies the exact weighted-amplitude replacement condition.
No full-grid exact blindness is asserted for this polar family.

## Scope and formal status

The contribution is the connected topology and moment classification, together
with actual smooth witnesses separating pointwise grid behavior, uniform trace
control, energy convergence and polar continuity. Existing copy algebra, source
moment products and energy envelopes are reused, not counted anew. These results
do not resolve polar closedness inside the exactly blind infinite-grid class.

Deep corpus search completed in 64.92 seconds; candidates were source-only and
largely outside the applicable source domain. Lexical fallback and direct reads
verified the actual copy moment multiplier, local-copy identities, exponential
energy envelope and full-line cosh product. Logs:
`/tmp/distant-copy-topology-research.txt`, `/tmp/distant-copy-polar-lexical.txt`.
No exhaustive external priority claim is made.

Dependency-closed paper proof complete. Lean certificate pending; not counted.
