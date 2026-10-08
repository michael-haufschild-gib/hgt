# Many-node correction cost at growing prime separation

Status, 8 October 2026: MH1 below is a classical-mechanism BRIDGE with a
closed paper proof, not a novelty claim or a new Lean theorem. MH2 is an
exact stronger conjecture, OPEN. Full PBAP remains OPEN. The preceding
one-node boundary C is formalized away from d=1; this document returns to
the broad-profile, simultaneous-constraint core of D2.

## Fixed actual source and quantifiers

Let phi be the existing `jointUnitBumpTest`. Fix W=log(2)/2 and
beta(u)=phi(u/W), independent of p. This is the actual smooth nonnegative
real source, with support in [0,W]. Write

    rho(y)=Re(EF.weilTest beta beta y),
    m=integral |beta|^2>0,
    B=integral beta>0.

Thus rho is smooth, even, nonnegative, supported in [-W,W], and
integral rho=B^2. Its cosine transform is |paperFT beta(T)|^2>=0.
These facts follow from the literal autocorrelation definition, Fubini and
the existing smooth compact source. No spectral positivity is assumed.

For each prime p>=5 set L=log(p)/2 and N=exp L=sqrt p. Let S_p consist of
the actual real-active nodes n with 2<=n<p and rho(log n-L)!=0. For any
finite index set I, nonnegative w_i and real t_i, put

    M=sum_i w_i,
    C(w,t)=sum_i w_i log(2+|t_i|).

Admissibility means the exact equations

    1+sum_i w_i cos(t_i(log n-L))=0       (n in S_p).

`jointClusterMixture_null_iff_active` identifies these with all literal
real integer-null constraints; no inactive-node or complex-null equations
are imposed. The full-system construction supplies examples at every M>1
and every sufficiently large prime. The base coefficient is fixed at one.

## MH1: a baseline that the corpus already supports

For every M0>1 and A>0, there is L0 such that every prime with L>=L0 and
every admissible correction with M<=M0 satisfies C(w,t)>=A L.
Equivalently the infimum of C/L tends to infinity at each fixed mass cap.
This differs from the already formalized M down to one limit at fixed p.

For every sufficiently large real L, define the finite sums

    Z_L=sum_(n>=2) rho(log n-L)/n,
    F_L(T)=Z_L^(-1) sum_(n>=2) rho(log n-L) cos(T(log n-L))/n.

Only n in [N exp(-W),N exp W] contribute. Nonnegative weights give
|F_L(T)|<=1 once Z_L>0. Exact admissibility gives
1+sum_i w_i F_L(t_i)=0. Inactive nodes contribute zero.

Here is a dependency-closed paper proof of the required uniform estimate:
for each fixed a>0,

    inf_(|T|<=N^a) F_L(T) >= -o(1).                         (1)

For low heights |T|<=N^(1/2), apply cellwise quadrature to
g_T(x)=rho(log x-L) exp(iT(log x-L))/x, extended by zero off its compact
positive support. On each unit cell, the fundamental theorem of calculus
bounds the sum-versus-integral error by integral |g_T'|. Summing cells gives

    |sum g_T(n)-integral g_T(x) dx|
      <= N^(-1) exp(W) [||rho'||_1+(1+|T|)||rho||_1].        (2)

The substitution y=log x-L turns the integral into integral rho(y)e^(iTy)dy,
whose real part is nonnegative. At T=0 the same bound gives Z_L->B^2>0.
Hence the normalized low-height lower error is O(N^(-1/2)), uniformly.

For N^(1/2)<=|T|<=N^a, let n0=ceil(N exp(-W)) and
m0=floor(N exp W)+1. Since exp(2W)=2, m0<=2n0+1. Choose a fixed integer
q>a+1 and k0=q+2. Eventually (k0-1)!<=n0,
8*pi*n0^(1/3)<=|T|, and |T|<=n0^q. The already proved
`routeT_lowShell_high_of_le_pow` pays the derivative schedule's upper window.
The general `dirichlet_block_sigma_saving_of_small_factorial`, with sigma=1,
therefore gives, uniformly for n0<=r<=m0,

    |sum_(n0<=n<r) n^(-1-i|T|)| <=2560 n0^(-eta),
    eta=1/(3*2^k0)>0.                                     (3)

Changing the sign of T conjugates this sum. Discrete Abel summation with
the real weight rho(log n-L) bounds the weighted sum by (3) times
||rho||_infinity+integral |rho'|. The variation bound follows because log n
is increasing and the intervening logarithmic intervals are disjoint.
Multiplication by exp(-iTL) does not change the norm. Dividing by Z_L proves
a uniform O_a(N^(-eta)) bound for the high-height part. Together with (2),
this proves (1), including the overlap and every intermediate height.

To finish MH1, use (1) with epsilon=1/(2M0) and horizon H=exp(2A L).
The low-height contribution to sum_i w_i F_L(t_i) is at least -1/2;
the remaining contribution is at least minus its total weight. The exact
value -1 forces at least 1/2 correction mass above H. Since log(2+|T|)>=0
everywhere, C(w,t)>=log(H)/2=A L. All constants depend only on the fixed
source, a or M0, never on the chosen finite correction.

Verdict: **BRIDGE**. The general derivative schedule already exists in the
corpus; a primary external parent is Arias de Reyna,
[Explicit van der Corput's d-th derivative estimate](https://arxiv.org/abs/2407.02094).
Quadrature, Abel summation and Fourier positivity complete its application.
Do not rebuild derivative tests or call this scientific novelty.

## Stronger conjecture MH2 and its incompatible competitor

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? The unresolved structural issue is
whether all active nodes together impose a frequency cost that dominates
the actual broad-profile pole scale, even with fixed correction mass.

**MH2:** for every M0>1 and every A>0 there is L0 such that, at every prime
with L>=L0, every admissible correction with M<=M0 satisfies

    C(w,t)>=A exp(L/2).                                   (4)

This is a cost-divergence law, stronger than merely a positive full-energy
sector. Its falsifiable competitor is: there exist M0>1 and K>0 and
arbitrarily large primes admitting exact corrections with M<=M0 and
C(w,t)<=K exp(L/2). Failure of (4) would not refute PBAP: a bounded cost on
this scale can still pay the exact signed energy, depending on constants.

MH2 cannot be deduced by exchanging quantifiers in MH1. The latter allows
an arbitrary fixed exponent a; it provides no estimate when a grows like
exp(L/2)/L. Likewise, a large value of one averaged Dirichlet polynomial
does not construct simultaneous exact cancellation at every active node.
Conversely, Kronecker recurrence supplies arbitrarily high exact corrections
but gives no cheap upper bound contradicting (4).

The implication from MH2 to a new energy sector is already elementary and
closed on paper. Let P=jointLaplaceNorm(beta,1/2)*jointLaplaceNorm(beta,-1/2).
The existing literal full-energy bound gives

    E(c)>=2m C(w,t)-(1+M0) C_L+2m log 2,
    C_L=2m(10+log4)+4 jointLogMoment(beta)
          +4(1+exp(L/2))(1+exp(-L/2))P.

The zero-modulation instance pays the seed term in this inequality;
both signed poles remain included. C_L/exp(L/2)->4P. Thus (4) would force
E(c)/exp(L/2)->+infinity uniformly at the fixed mass cap. Actual physical
mass is 2m(1+M)<=2m(1+M0), so the same divergence holds per unit physical
mass. This would settle the large-prime fixed-source part of D2, but would
still leave varying profiles, unbounded correction mass and the full cone.

**[OPEN CORE]** Prove (4), or construct exact admissible counterfamilies.
Neither the fixed-order derivative schedule nor the verified one-node
certificate pays this scale. A pointwise estimate for one positive weighted
sum is only a sufficient mechanism and may fail through resonance; the
conjecture concerns the whole vector of simultaneous constraints.

Preliminary verdict for MH2: **SURVIVES PRELIMINARY ATTACK**, not proved and
with scientific novelty unestablished. No Lean theorem assumes (4).
Quantitative recurrence must be tested against it before choosing a proof
route. The primary-source audit located Korolev--Rezvyakova's
[local Kronecker theorem](https://www.mathnet.ru/php/archive.phtml?jrnid=cheb&option_lang=eng&paperid=1257&wshow=paper)
and the Gonek--Montgomery quantitative ancestry cited there. The search
abstract supplies an upper recurrence bound, not a lower cost bound;
the full PDF fetch failed. Xu--Yang's
[extreme-value paper](https://arxiv.org/abs/2303.06739) and Hough's
[angle-of-large-values paper](https://www.math.stonybrook.edu/~rdhough/angle_results.pdf)
are adversarial parents for a single-average approach, not proofs of an
admissible cheap correction. No unverified asymptotic from those papers is
used in the proof of MH1 or the conditional consequence above.

## Internal search audit and next actions

All returned candidates and source-argument statements were inspected in
the deep searches `wp01-log-phase-polynomial-horizon-20261008.json`,
`wp01-weighted-horizon-exact-audit-20261008.json`,
`wp01-many-node-height-cost-audit-20261008.json`, and
`wp01-positive-spectral-atom-audit-20261008.json`, saved under /tmp.
The last three report partial=true with 68,768/68,769/68,770 covered files,
reranking or semantic deadlines and mostly pending compiler metadata.
No conclusion of nonexistence follows from those partial searches.
The proposed spectral-kernel ingredient chain assumes `WeilPositiveFull`
and would be circular here; the phase-increment/disk-height chain is
inapplicable. The derivative schedule was checked directly in source.

Continue with the exact MH2 statement and the quantitative recurrence
attack; do not formalize another conditional wrapper. If that attack kills
MH2, extract the sharp surviving cost or energy law, close its paper proof,
and formalize it. Keep MH1 available as an audited baseline, not a substitute
for the exponential scale.

### Quantitative recurrence attack

[Maksimova, arXiv:2405.07051v1](https://arxiv.org/html/2405.07051v1),
Theorem C, reproduces Gonek--Montgomery's explicit bound: a coordinate box
with tolerances epsilon_j is hit in every interval of length 4/delta, where
delta is the least nonzero bounded integer linear form in the frequencies,
and |m_j|<=ceil(epsilon_j^(-1) log(r/epsilon_j)). Her Theorem1 supplies a
transference variant. The full statements were read, rather than inferring
an effective bound from the abstract.

For our prime coordinates, multiply a linear form by 4pi to obtain log(A/B)
for distinct positive integers A,B, by unique factorization. If coordinate
coefficients have size at most H, then

    max(A,B)<=exp(H*(2 sum_(q<=N exp W) log q+log p)),
    |log(A/B)|>=1/max(A,B).

Thus this elementary application supplies an upper recurrence horizon whose
logarithm is at most a constant plus H*(2 sum log q+log p). It does not
supply a lower recurrence bound. The resulting displayed guarantee, with
its many prime coordinates and shrinking tolerance, does not give the
O(exp(L/2)) correction cost needed to kill MH2. More fundamentally, a single
near-antiphase visit is only approximate; exact finite positive quadrature
still needs a quantitative interiority and repair argument. No approximate
visit is recorded as an exact null mixture.

Source spot-checks: `primeTorus_kronecker_dense`, `exists_phase_witness`,
`exists_simultaneous_phase_recurrence`, and the actual
`exists_positive_joint_phase_correction` contain no upper height estimate.
The last uses forward orbit closure plus finite-dimensional interiority.
This attack leaves MH2 open. Next use the whole vector of constraints to
construct a cost-sensitive separating polynomial, or quantitatively realize
an exact cheap convex combination; pointwise recurrence alone decides neither.

The exact-statement deep follow-up `wp01-mh2-exact-statement-20261008.json`
exited normally with partial=true, 68,773 covered files and a semantic deadline.
All20 candidate and20 source-argument statements plus its ingredient set
were inspected. It recovers the earlier two-node minorant and unquantified
opposite-point closure, not (4). The proposed shifted-phase/log-exp ingredient
chain has no applicable cost implication. Every owned search has now exited.
