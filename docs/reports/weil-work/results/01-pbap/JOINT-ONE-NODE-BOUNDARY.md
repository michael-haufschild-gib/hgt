# Critical width of a nearest-node certificate

Status, 2026-10-08: conjecture C is formalized for every fixed d<1 and d>1,
including actual prime lags, negative seeds, active nodes, the full null-mixture
margin and nonemptiness at every correction mass M>1. Six new leaves,
`WeilWorkPBAPJointUniformHigh` and `WeilWorkPBAPJointBoundary{Seed,Obstruction,
Certificate,Prime,Null}`, pass targeted builds, final direct-source audits
and all 26 public axiom checks. Their four supporting leaves were audited
previously. The exact d=1 boundary and full PBAP remain OPEN.
No scientific novelty claim. This is a boundary of one particular certificate,
not an obstruction to simultaneous integer-null positivity.

## Exact proposed statements

Use the actual nonnegative real unit bump phi from
`WeilWorkPBAPJointWidthSector.jointUnitBumpTest`. Put
B=integral phi>0, m0=integral phi^2>0, kappa=m0/B^2. For a prime p tending to
infinity define L=(log p)/2, n=floor(exp L), delta=L-log n,
lambda=log(1/delta)/L, and alpha*=lambda+1/2. Given alpha>0 put
W=kappa*alpha*L*exp(-L/2), beta(u)=phi(u/W), m=W*m0, and let e(T) be the
literal full paired two-cluster energy `jointPairFullEnergy beta L T`.
All limits below are over primes; their constants depend only on phi and,
where indicated, a fixed positive gap d.

**Boundary conjecture B:** at alpha=alpha*, eventually

    e(0)+e(pi/delta) <= m*(-2*log L+C_phi) < 0.

Consequently no real c satisfies -c*cos(delta*T)<=e(T) for every real T.
The phase tests at 0 and pi/delta force the opposite inequality on their sum.

**Positive survivor S:** for each fixed 0<d<1, at alpha=alpha*-d, eventually
there is an actual c>0 such that, for every real T,

    e(T)+c*cos(delta*T) >= (d/4)*m*L.

The nearest integer is an actual active autocorrelation node. Every finite
nonnegative real-null correction therefore has positive full energy, with
the corresponding physical-mass margin. Existing simultaneous correction
construction makes this sector nonempty at every prescribed correction
mass M>1. S motivated the sharper logarithmic transition C below. The
production capstones formalize C; this earlier fixed-gap formulation is not
exported as a separate Lean theorem.

**Sharper conjecture C, exposed by the three-band audit:** fix any real d
and set alpha=lambda+1/2-d*log(L)/L. If d<1, eventually no one-node
certificate exists, since

    e(0)+e(pi/delta) <= 2*(d-1)*m*log L+O(m) < 0.

If d>1, eventually the actual positive coefficient

    c=m*(2*lambda*L-(d-1)*log L)

satisfies e(T)+c*cos(delta*T)>=(d-1)*m*log(L)/2 for all real T.
Every actual real-null correction then has full energy at least
(d-1)*log(L)/4 times its physical mass. The exact d=1 boundary is not
decided here. This strongest current survivor is now formalized, including
the actual-prime/null-mixture transfer and nonemptiness.

## Dependency-closed paper proof

The prime p is not a square. For large p, 2<=n<sqrt(p) and n^2<=p-1.
The elementary bound log x>=1-1/x, x>=1, gives

    1/(2*p) <= delta=(1/2)*log(p/n^2) <= 2*exp(-L).

The upper bound is the existing floor-exponential lag estimate. Hence
1-log(2)/L<=lambda<=2+log(2)/L. In both statements alpha is bounded above
and bounded away from zero, W tends to zero, and eventually 0<W<=1 and
2W<L. Also delta/W tends to zero. Continuity of phi's autocorrelation and
its positive value m0 at zero imply actual activity at the nearest node.

Write J1(phi)=integral |u|*|F(phi)(u)|^2 du, which is finite by the corpus
linear-weight Fourier integrability theorem. Dilation gives exactly
J1(beta)=J1(phi). The paired density rho is nonnegative, has exact normalized
mass integral rho/(2*pi)=2m, and equals

    (1-cos(xi*L))*(|F(beta)(xi-T)|^2+|F(beta)(xi+T)|^2).

For T>=0 and either sign, the triangle inequality and log(1+x)<=x give

    gamma(xi) <= log(1+T)+4+|xi +/- T|/(1+T).

Subtract the constant A=log(1+T)+4 before estimating the interference
factor by 2. This yields the pointwise bound

    rho*(gamma-A) <= 2/(1+T) *
      (|xi-T|*|F(beta)(xi-T)|^2+|xi+T|*|F(beta)(xi+T)|^2).

Gamma integrability is already proved for the actual smooth compact tests;
the right side is integrable by translation of J1. Integrate, retaining
the exact mass in the constant term:

    Gamma(pair,T) <= 2m*(log(1+T)+4)+4*J1(phi)/(2*pi*(1+T)).       (1)

The existing two-pole estimate, with D=integral |phi''|, gives

    |Pole(pair,T)| <= 4*(1+exp(L/2))*(1+exp(-L/2))*
      (exp(W/2)*D/(W*T^2))^2,                  T != 0.           (2)

At T*=pi/delta, T*>=pi*exp(L)/2, so (1)'s remainder divided by m is
O(exp(-L/2)/L), and (2) divided by m is O(exp(-2L)/L^3).
Furthermore log(1+T*)=lambda*L+log(pi)+o(1). Therefore

    e(T*)/m <= 2*lambda*L+8+2*log(pi)+o(1).                     (3)

The existing uniform seed Gamma theorem gives

    Gamma(seed)/m = -2*log W+O(1)
      = L-2*log L-2*log(kappa*alpha)+O(1).                     (4)

Nonnegativity of phi gives a useful one-sided pole bound without invoking
an unquantified continuity rate. Fubini and symmetry yield

    Pole(beta)=2*integral integral beta(u)*beta(v)*cosh((u-v)/2)
      >=2*W^2*B^2.

All integrands are supported on a compact square and continuous. Multiplying
by the nonpositive exact cluster factor 2*(1-cosh(L/2)) gives

    Pole(seed)/m <= -2*alpha*L*(1-exp(-L/2))^2.                 (5)

At alpha=lambda+1/2, adding (3)--(5) cancels every term proportional to
lambda*L. The bounded alpha factors and vanishing exponential errors leave
e(0)+e(T*)<=m*(-2*log L+C_phi) eventually. Since log L tends to infinity,
this proves B, including its strict sign and the two-point contradiction.

For S, a quantitative seed pole remainder is also needed. On the support,
|u-v|<=W, so 1<=cosh((u-v)/2)<=cosh(W/2). Thus the beta pole lies between
2*W^2*B^2 and 2*W^2*B^2*cosh(W/2). Taylor's theorem on [0,1/2] gives
cosh(W/2)-1<=C*W^2, with a constant independent of W. Multiplication by the
cluster factor and division by m now show

    e(0)/m = (1-2*alpha)*L-2*log L+O(1).                      (6)

Indeed L*W^2 and L*exp(-L/2) tend to zero uniformly for the bounded alpha
range. This is a quantitative bound, not a rate inferred from continuity.
More precisely, the exponential Taylor remainder gives C=1/4 for 0<W<=1,
and hence |P_phi(W)-2*B^2|<=B^2*W^2/2. Combining it directly with the
existing Gamma estimate gives the useful uniform unnormalized formula

    |e(0)+2*W*m0*log W+4*(cosh(L/2)-1)*W^2*B^2|
      <= W*C_gamma(phi)+(cosh(L/2)-1)*W^4*B^2.

The Gamma cost C_gamma is the literal fixed integral `jointSeedLogCost`.
This formula keeps every error explicit before any variable-width limit.

Choose epsilon=min(d/4,1/8), H=exp(-epsilon*L)/delta and
c=(2*lambda-d)*m*L>0. In the low band |T|<=H, cos(delta*T)>=
1-exp(-2*epsilon*L)/2. The already proved nonnegative modulation kernel
gives e(T)>=e(0). Substitute alpha=lambda+1/2-d in (6); it follows that
e(T)+c*cos(delta*T)>= (d/2)*m*L eventually, uniformly in this band.

In the high band, use the existing exact-mass lower Gamma and two-pole
bound. At |T|>=H, log(|T|/2)>= (lambda-epsilon)*L-log 2. The normalized
central-mass loss is bounded by a constant times
log(|T|/2)/(W^3*|T|^3); the normalized pole loss by a constant times
exp(L/2)/(W^3*|T|^4). Both tend uniformly to zero: lambda>=1-o(1) and
epsilon<=1/8 leave strictly negative exponential exponents. For the first
bound one may use log(|T|/2)<=|T| and |T|>=H, giving an exponent at most
(-1/2+2*epsilon)*L. Consequently

    e(T)/m >= 2*(lambda-epsilon)*L-O(1).

Using cos>=-1 gives e(T)+c*cos(delta*T)>=
(d-2*epsilon)*m*L-O(m)>=(d/4)*m*L eventually. Evenness handles negative T.
This proves the all-frequency certificate in S. Summing it and using the
literal active-node null identity yields the stated correction-energy
margin, exactly as in the already compiled width-sector capstone. Every
test is an actual smooth compact dilation; no energy, pole, phase-cost,
activity or certificate premise is being assumed.

For C, alpha remains bounded above and away from zero. Equations (3)--(6)
apply unchanged, with

    e(0)/m = -2*lambda*L+2*(d-1)*log L+O(1).

For d<1, equation (3) immediately gives the asserted strict two-point
failure. For d>1 use the displayed actual c and split into three bands.
First, |T|<=exp(7L/8): the phase-square loss is O(exp(-L/4)), so the exact
seed minimum gives e(T)+c*cos(delta*T)>=
m*((d-1)*log L-O(1)-O(L*exp(-L/4))). Second,
exp(7L/8)<=|T|<=pi/(2*delta): cos(delta*T)>=0, while the existing uniform
high-frequency estimates give e(T)>=m*(7L/4-O(1)-o(1)). Third,
|T|>=pi/(2*delta): the same exact-mass lower estimate gives
e(T)>=m*(2*lambda*L-O(1)-o(1)), hence after using cos>=-1 the required
margin is m*((d-1)*log L-O(1)-o(1)). The second band exists eventually
because delta<=2*exp(-L). Each bound exceeds
(d-1)*m*log(L)/2 eventually. Summation against the active-node null
identity and the exact physical mass 2m*(1+M) gives the stated margin.
No unproved monotonicity of e(T) is used: the middle band only needs its
already available positive lower bound and the sign of the cosine.

## Hostile audit and ancestry

Question used for selection: given the exact internal and external frontier,
what would a Fields Medal-winning mathematician conjecture? The chosen
answer is the explicit transition C, rather than another coefficient-free
energy bound. It could fail through a lost mass factor, a surviving pole,
an arithmetic lag outside its claimed scale, or a low-frequency dip missed
by the certificate. If true, it separates exactly the leading logarithmic
widths where one active node can and cannot pay the negative seed. Failure
would identify which scale balance must be replaced. No full-cone result
follows from either outcome.

Verdict for C: **PROVED AND FORMALIZED AWAY FROM d=1**, with scientific novelty still
unestablished. The supporting upper estimate and pole bounds are **BRIDGE**,
not separate new-science claims. The paper argument survives the sign,
normalization, uniformity and integrability audit above; all six Lean leaves
and their final audits now pass.
The coefficient 2m in
(1), the negative multiplier in (5), the quantitative rather than merely
continuous remainder in (6), and the non-square arithmetic bound are essential.
Boundary B alone does not rule out a certificate with several integer nodes.
S establishes the leading width boundary for fixed gaps. The separate
three-band argument C identifies the coefficient of the log(L)/L transition
layer for this family, but does not decide its bounded 1/L correction or d=1.

Corpus searches: full-target lexical audit and the deep upper-energy audit
in `/tmp/wp01-full-target-20261008-next.json` and
`/tmp/wp01-boundary-upper-20261008.json`. The latter reports partial=false,
68,691 covered files, incomplete refresh and pending compiler metadata.
All returned candidates, source arguments and ingredient sets were inspected.
Existing width-sector results supply the lower estimates and alpha=1 survivor;
conditional full-positivity/RH declarations do not supply (1) or the sign.

External primary-source audit: Suzuki, arXiv:2606.09096v2; Zhu,
arXiv:2608.24827v2; Connes--Consani, arXiv:2006.13771; Groskin,
arXiv:2607.02828v3. The inspected abstracts/frameworks concern the full Weil
form, fixed-window spectra or finite truncation/tail certification. No exact
nearest-node width boundary was located. Absence from these searches does
not establish novelty; the modulation/Gamma asymptotic ingredients are
standard analysis. No numerical claim from these sources is used.
Exact-mechanism searches were repeated after C was stated. Their relevant
older primary hit was Connes--Consani,
[The Scaling Hamiltonian](https://arxiv.org/abs/1910.14368), concerning a
semilocal operator framework and limitations of an attempted positivity
argument. No theorem from it is imported into this proof; the other returned
hits on width/thresholds were unrelated. The novelty verdict remains provisional.

## Uniform high-frequency bridge (implementation checkpoint)

For any fixed source of positive mass and fixed κ>0, put W₀=κL exp(-L/2).
Uniformly over W₀≤W≤1 and |T|≥exp(7L/8), the actual paired energy satisfies,
for all sufficiently large L,

`2 log|T| − (2(log 2+10+log 4)+1) ≤ e(T)/(W m₀) ≤ 2 log(1+|T|)+9`.

Proof: divide the existing dilated high-frequency inequality by Wm₀. Both
inverse-cubic width errors decrease as W increases, so replace W by W₀.
The two resulting bounds are `Cγ L exp(-L/4)` and `Cp L exp(-3L/2)`.
For the upper bound, the first Fourier moment is dilation invariant; its
normalized error is at most `C₁ exp(-3L/8)`, and the same signed-pole error
applies. All three explicit remainders tend to zero. Evenness gives signed T.
This pays the final-band coefficient without replacing log|T| by its threshold.
The bridge is standard analysis, not an independent scientific novelty claim.

## Uniform seed bridge (implementation checkpoint)

Let κ=m₀/B², W=κK exp(-L/2), and L≤K≤3L. Dividing the full seed expansion
by Wm₀ gives pole center `2K(1-exp(-L/2))²`. Its difference from `2K` is
at most `12L exp(-L/2)`. The normalized pole remainder is at most
`27κ²L³ exp(-L)`. Thus

`|e(0)/(Wm₀)+2log W+2K| ≤ Cγ/m₀+27κ²L³exp(-L)+12Lexp(-L/2)`.

Both variable terms vanish uniformly in K. For `K=L/2+s-d log L`, exact
logarithm algebra gives

`2log W+2K=2s-2(d-1)log L+2log(κK/L)`.

Since κ≤κK/L≤3κ, its last term is bounded by
`2(|log κ|+|log(3κ)|)`. A single source-defined constant therefore bounds
`|e(0)/(Wm₀)+2s-2(d-1)log L|` for the whole permitted lag range.
The actual-prime specialization uses the verified prime lag bounds, without
an assumed phase-scale or energy estimate.
