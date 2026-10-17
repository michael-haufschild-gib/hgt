# Weight growth, Taylor order and sharp Nyquist residuals

## Scope and status

Dependency-closed paper proof, with the paper and corpus audit complete. Lean
formalization is in progress, and no contribution is counted yet.
This continues infinite-grid tail rigidity for general signed correlations.
The field guide `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` is read-only.

The preceding package constructs the constant cell producer for cosh(x/2).
Here the weight itself is approximated to arbitrary order. No derivative or
spectral-moment bound on a varying source is assumed. The theorem classifies
when the resulting correction is bounded and gives actual smooth sources that
certify its sharpness, even with normalized Levy energy tending to zero.

## 1. Explicit producer and main classification

Fix beta>0 and an integer m>=0. Write k=m+1, and let

    w_beta(x)=cosh(beta x),
    J_(beta,j)(x)=beta^j [exp(beta x)+(-1)^j exp(-beta x)]/2.

Direct differentiation gives w_beta^(j)=J_(beta,j). For n>=1, put

    a_n=log n, b_n=log(n+1), delta_n=b_n-a_n,
    p_(beta,m,n)(x)=sum_(j=0..m) J_(beta,j)(a_n)(x-a_n)^j/j!,
    e_(beta,m,n)(x)=w_beta(x)-p_(beta,m,n)(x), x in [a_n,b_n],
    alpha_(beta,m,n)=integral_[a_n,b_n] e_(beta,m,n).

Assemble e_(beta,m) using the half-open cells (a_n,b_n], and set it to zero
on (-infinity,0]. Let e_(beta,m,N) be its restriction to (log N,infinity),
where N>=1. All endpoint choices differ only on a countable null set.

**Theorem.** These actual kernels are nonnegative and locally integrable. They
are integrable on the entire half-line exactly when beta<m+1. With

    c_(beta,m)=beta^(m+1)/(2(m+2)!),

the precise cell asymptotic is

    alpha_(beta,m,n)/n^(beta-m-2) -> c_(beta,m).

If q=m+1-beta>0, the tail mass A_(beta,m,N)=sum_(n>=N) alpha_(beta,m,n) obeys

    A_(beta,m,N) <= B_(beta,m)(1+1/q) N^(-q),
    B_(beta,m)=2^beta beta^(m+1)/(m+2)!,
    A_(beta,m,N)/N^(-q) -> c_(beta,m)/q.

At beta=m+1, partial masses through cell M, starting at any fixed N, divided
by log M tend to c_(beta,m). If beta>m+1, division by M^(beta-m-1) instead
gives limit c_(beta,m)/(beta-m-1). In both cases every infinite tail has
infinite mass. For beta=0, the weight is constant and every residual is zero.

## 2. Positivity and an explicit cell bound

For every j>=0 and x>=0, J_(beta,j)(x)>=0: the even derivatives contain
cosh(beta x), and the odd derivatives contain sinh(beta x). Taylor's integral
remainder gives, for 0<=t<=delta_n,

    e_(beta,m,n)(a_n+t)
      = 1/(k-1)! integral_0^t (t-s)^(k-1) J_(beta,k)(a_n+s) ds.

This formula follows by integration by parts k-1 times and the fundamental
theorem of calculus; the successive boundary terms are precisely the displayed
finite Taylor polynomial. All functions are smooth on the finite interval,
so each integration and boundary term is legitimate. The kernel in the formula
is nonnegative, proving positivity of the residual on every cell, including n=1.

The elementary logarithmic bounds are

    1/(n+1) <= delta_n <= 1/n.

They follow by integrating 1/u between n and n+1. On the cell,

    J_(beta,k)(a_n+s) <= beta^k exp(beta(a_n+s))
      <= beta^k (n+1)^beta <= beta^k 2^beta n^beta.

Integrating the remainder and then t from zero to delta_n gives

    0 <= alpha_(beta,m,n)
      <= [2^beta beta^k/(k+1)!] n^beta delta_n^(k+1)
      <= B_(beta,m) n^(beta-m-2).

Thus the upper bound is explicit for every cell, not an asymptotic assumption.

## 3. Sharp cell asymptotic

For 0<=s<=delta_n, the exact derivative formula is

    J_(beta,k)(a_n+s) / [(beta^k/2)n^beta]
      = exp(beta s)+(-1)^k n^(-2beta)exp(-beta s).

Its difference from one is bounded in absolute value by

    exp(beta/n)-1+n^(-2beta),

which tends to zero because beta>0. This is a uniform estimate on the entire
shrinking cell, including both endpoints. Given epsilon in (0,1), for all
sufficiently large n the derivative lies between (1-epsilon) and (1+epsilon)
times (beta^k/2)n^beta. Insert these two bounds into the nonnegative integral
remainder and integrate once more. The resulting cell mass lies between

    (1-epsilon)c_(beta,m)n^beta delta_n^(k+1)
      and (1+epsilon)c_(beta,m)n^beta delta_n^(k+1).

Since n/(n+1)<=n delta_n<=1, the factor n delta_n tends to one. Dividing by
n^(beta-k-1), and then letting epsilon tend to zero, proves the stated cell
asymptotic. In particular its leading constant is strictly positive.

## 4. Summability, divergence and sharp tail constants

Put p=beta-m-2. The preceding asymptotic compares alpha_n, above and below,
with positive constant multiples of n^p outside a finite prefix. For p<-1,
monotonicity of x^p gives

    integral_N^infinity x^p dx <= sum_(n>=N) n^p
      <= N^p+integral_N^infinity x^p dx.

The integral is N^(p+1)/(-p-1). This proves convergence, the explicit bound
in Section 1, and sum_(n>=N) n^p/N^(p+1)->1/(-p-1). Apply the two-sided
epsilon comparison from Section 3 to obtain the sharp tail constant.

For p=-1, comparison with integral 1/x gives
sum_(n=N..M) 1/n/log M ->1 for fixed N. For p>-1, comparison on adjacent
unit intervals with integral x^p gives
sum_(n=N..M) n^p/M^(p+1)->1/(p+1). For p>=0 use the increasing-function
comparison; for -1<p<0 use the decreasing-function comparison. In both cases
the endpoint discrepancy is bounded by a constant plus M^max(p,0), which is
negligible after division by M^(p+1). The finite prefix removed by the cell
comparison is also negligible. Taking epsilon to zero gives both divergent
partial-mass asymptotics and their positive constants.

The half-open cells form a disjoint measurable partition of (0,infinity).
On a bounded interval only finitely many cells occur. Their continuous residuals
give a measurable locally integrable kernel. Countable additivity for the
nonnegative integrals identifies its mass with the sum of the cell masses.
This proves the exact integrability classification without any cancellation
or subtraction of divergent quantities.

## 5. Exact bounded correction and produced cell moments

Assume beta<m+1. For a bounded continuous real H define

    R_(beta,m,N)(H)=integral H(x)e_(beta,m,N)(x) dx.

Absolute integrability follows from |H e|<=||H||_infinity e. The functional is
positive, linear and bounded, with

    |R_(beta,m,N)(H)| <= A_(beta,m,N)||H||_infinity,
    ||R_(beta,m,N)|| = A_(beta,m,N).

The lower norm bound is attained by H=1. Its cell-integral representation is
absolutely summable, and its norm tends to zero as the tail starts farther out.
For H and G, the residual difference is at most A_(beta,m,N)||H-G||_infinity.

For continuous compactly supported H define the explicit producer

    Q_(beta,m,N)(H)=sum_(n>=N) sum_(j=0..m)
      J_(beta,j)(log n)/j! * integral_[log n,log(n+1)] H(x)(x-log n)^j dx.

Both sums over cells are finite: once log n exceeds the support bound, H is
zero on the entire cell. The cell identity w_beta=p+e, finite integral
linearity and additivity over consecutive cells give

    integral_(log N,infinity) H(x)cosh(beta x) dx
      = Q_(beta,m,N)(H)+R_(beta,m,N)(H).

This exact identity holds for compact H at every beta>=0 and every m, even
above the integrability threshold: in that case R means the finite integral
of the compact input against the locally integrable kernel, not a bounded
functional on all bounded inputs. Below the threshold the explicit error bound
from Section 1 is valid uniformly in H. Global uniform convergence of compact
inputs makes residuals converge, so continuity of their polar integrals is
equivalent to continuity of these actual produced cell moments.

For actual normalized compact-source correlations, ||H||_infinity<=1.
Consequently every subcritical error bound is independent of source support,
source count, energy and derivatives. The approximation uses signed cell
moments, without replacing them by absolute values or asserting a node formula.

## 6. One actual smooth source family certifies all thresholds

Choose the nonnegative smooth compact bump f centered at zero with inner radius
1/2 and outer radius 1, so f(0)=1. This is the actual ContDiffBump used in the proof of
`exists_smooth_source_positive_polar_moment` in `DistantCopyPolarTopology`.
Let R=integral f^2>0 and H(x)=integral f(u)f(u+x) du/R. Then H is smooth,
compactly supported, 0<=H<=1, and H(0)=1. Continuity supplies r>0 such that
H(x)>=1/2 for 0<=x<=r.

Set lambda_j=j+1 and f_j(u)=f(u/lambda_j). Change of variables gives

    autocorr(f_j)(0)=lambda_j R>0,
    H_j(x)=H(x/lambda_j).

Each f_j is an actual nonnegative smooth compact source. The family is chosen
once, independently of beta, m and N. Its correlations satisfy 0<=H_j<=1,
converge pointwise to one, and are at least 1/2 on [0,r lambda_j].

Its normalized Levy energies have an unconditional quantitative bound. The
existing `exists_autocorr_increment_linear_bound` in `BroadSpectralCostRealization`
derives M_0>=0 with R-autocorr(f)(x)<=M_0|x| for every x. Its proof derives a
finite Lipschitz constant for this fixed compact smooth f and integrates the
translation difference against |f|. Thus M=M_0/R is a derived finite constant,
and 0<=1-H(t)<=M|t|. Consequently, for every j and x>0,

    0 <= 1-H_j(x) <= Mx/lambda_j.

The actual first moment J_1=integral_(0,infinity) x w_arch(x) dx is finite and
nonnegative. The same module proves this using the explicit bound

    x w_arch(x) <= (2x+1) exp(-x/2), x>0.

Multiplication by the positive Levy weight and integration now give

    0 <= E(f_j) <= M J_1/lambda_j = K/(j+1),  K=M J_1>=0.

In particular the energies tend to zero under one common ceiling K. This is
the scaling calculation already present in the proof of
`exists_source_normalized_energy_lt`, now retained for the entire explicit
family. All regularity, mass, integrability and energy properties are derived
from the one concrete source; no varying-source regularity bound is assumed.

Now fix any beta>0, m>=0 and N>=1. Below the threshold, domination by the
integrable residual kernel gives

    R_(beta,m,N)(H_j) -> A_(beta,m,N).

At or above the threshold, for r lambda_j>log N, positivity gives

    R_(beta,m,N)(H_j)
      >= (1/2) integral_(log N,r lambda_j) e_(beta,m)(x) dx -> infinity.

The last limit follows from the divergent positive cell masses: any prescribed
finite prefix is eventually contained in that interval. The exact compact-input
identity identifies these residuals with the differences between actual polar
integrals and their produced cell moments.

This also proves sharpness within the actual smooth correlation cone below the
threshold. For every energy allowance epsilon>0 and tolerance eta>0, some actual
smooth compact source in this one family satisfies E<=epsilon and

    A_(beta,m,N)-eta <= R_(beta,m,N)(H_j) <= A_(beta,m,N).

Thus A_(beta,m,N) remains the optimal error bound even after imposing any
positive energy ceiling. Above the threshold, the same family disproves a
finite error bound based solely on such a ceiling.

These wide-source families do not have uniform signed grid tails. For any
fixed logarithmic node, H_j there tends to one, while each individual compact
correlation eventually vanishes along the grid. No claim of global uniform
correlation convergence, compact correlation closure, or a counterexample
under uniform trace tightness is made.

## 7. Minimal order and two calibration cases

For beta>0, the least integer degree giving a bounded correction is floor(beta),
because beta<m+1 holds exactly when floor(beta)<=m. This is a sharp producer
hierarchy with no source-regularity interface.

At beta=1/2,m=0, the construction is exactly the preceding Nyquist producer,
and its norm has the sharper asymptotic A_N~1/(4 sqrt(N)). At beta=1,m=0,
partial residual masses grow as (1/4)log M. The linear weight producer m=1
restores integrability at that same beta, with A_N~1/(12N).

Taylor's theorem, the power-series convergence test and dominated convergence
are established tools, not new contributions. The connected contribution
is the exact logarithmic-cell weight/order classification, its explicit bounded
producer and norm asymptotics, and the single actual low-energy smooth family
that proves sharpness and the failure of every insufficient producer order.
No prime quadrature, arithmetic positivity or RH claim is included.

## 8. Formal certificate

The complete result is formalized in seventeen direct Lean leaves, with
159 theorems and 27 definitions. All 186 public declarations have scratch
axiom audits using only standard logical axioms; all API entries, imports,
and source hashes are checked. The certificate is
`docs/drafts/pipeline/3-formalized/nyquist-weight-order-threshold-2026-10-17.md`.
It records five unrelated global lint failures; none concerns this package.

Lean uses zero-based cell k with n=k+1, tail N starting at log(N+1), and
prefixes containing M cells. Thus its displayed normalizations are log(M+1)
and (M+1)^(beta-m-1), with the same sharp constants as the fixed-index-shift
limits above. The degree-zero beta=1/2 producer, kernel, and cell/tail masses
are proved equal to the original Nyquist polar construction.
