# Origin-to-collar transport with an exact origin budget

This note develops the finite logarithmic-grid problem independently of any RH application.
Novelty is assessed only against the inspected local corpus; no claim of external novelty is made.

## Theorem: overlap-safe transport and optimal signed-coset weights

Let N ≥ 2 be an integer, L = log N, δ = (log 2)/2, and let h be a continuous real positive-definite correlation with R = h(0). Assume h(log n) = 0 for 2 ≤ n ≤ N. These define the admissible class; no derivative, polar-moment, or unproved analytic estimate is assumed. Put

\[
 w(x)=e^{x/2}/\sinh x,\qquad D(x)=R-h(x)\ge0.
\]

The energy below is a nonnegative extended Lebesgue integral, so the assertion also covers infinite energy. A real-valued Bochner integral without an integrability proof would not suffice.

For each n in {2,…,N}, choose a measurable nonnegative physical share ρ_n, supported in

\[
 E_n=(\log n-\delta,\log n+\delta)\cap(0,L),
 \qquad \sum_{n=2}^N\rho_n(x)\le1.
\]

Let C_m be the finite chain of integers n = m 2^k in {2,…,N}, for each odd m ≤ N. For σ ∈ {−1,+1}, define

\[
 a_{n,\sigma}(y)=w(\log n+\sigma y)\rho_n(\log n+\sigma y),\quad 0<y<\delta,
\]

with zero value outside E_n. In particular the right collar at N contributes zero, and other collars crossing L are truncated. Define

\[
 q_{m,\sigma}(y)=\left(\sum_{n\in C_m}a_{n,\sigma}(y)^2\right)^{1/2},
 \quad A(y)=\sum_{m,\sigma}q_{m,\sigma}(y),
 \quad B(y)=\sum_{n,\sigma}a_{n,\sigma}(y).
\]

Then

\[
 \boxed{\quad
 \int_0^L D(x)w(x)\,dx
 \ \ge R\int_0^\delta
 \left[w(y)+B(y)-\sqrt{w(y)^2+A(y)^2}\right]dy.
 \quad} \tag{1}
\]

The bracket K(y) is measurable, nonnegative, bounded, and integrable. It satisfies

\[
 B-\frac{A^2}{2w}\le K\le B,\qquad
 K=B-\frac{A^2}{\sqrt{w^2+A^2}+w}. \tag{2}
\]

For fixed physical shares ρ, the optimal origin allocations across the signed chains are

\[
 \boxed{\theta_{m,\sigma}(y)=q_{m,\sigma}(y)/A(y)}\quad(A(y)>0). \tag{3}
\]

On A = 0, every probability allocation is optimal. A coset-only description uses
θ_m = (q_{m,−}+q_{m,+})/A, followed by conditional sign shares q_{m,σ}/(q_{m,−}+q_{m,+}); zero denominators may be assigned arbitrarily. Using θ_m independently for both signs spends the origin budget twice.

## Complete proof

Positive definiteness gives |h(x)| ≤ R and R ≥ 0 by its two-point Gram matrices. For a fixed m and sign, the vectors at shifts 0 and log n, n ∈ C_m, are mutually orthogonal: each log n is a zero, and each difference of distinct log nodes is the logarithm of an integer power of 2 between 2 and N, up to sign. Real positive-definite h is even. Bessel therefore gives

\[
 h(y)^2+\sum_{n\in C_m}h(\log n+\sigma y)^2\le R^2. \tag{4}
\]

For an origin allocation α_j ≥ 0, with j=(m,σ) and Σ_j α_j = W = w(y), the one-chain sphere bound gives

\[
 \alpha_j D(y)+\sum_{n\in C_m}a_{n,\sigma}D(\log n+\sigma y)
 \ge R\left[\alpha_j+\sum_{n\in C_m}a_{n,\sigma}
       -\sqrt{\alpha_j^2+q_j^2}\right].
\]

The Euclidean triangle inequality for vectors (α_j,q_j) implies

\[
 \sum_j\sqrt{\alpha_j^2+q_j^2}\ge\sqrt{W^2+A^2}.
\]

For A>0 choose α_j=Wq_j/A. All vectors are nonnegative multiples of (W,A), so equality holds. For A=0, all q_j=0 and every allocation has cost Σ_j α_j=W. This proves the exact minimum, with no optimization existence assumption. Since W>0, A>0, equality in the triangle inequality forces α_j=Wq_j/A, including α_j=0 on q_j=0. Thus the allocation is unique whenever A>0. Sum the chain bounds at this allocation to obtain

\[
 RK(y)\le w(y)D(y)+\sum_{n,\sigma}a_{n,\sigma}(y)D(\log n+\sigma y). \tag{5}
\]

This is also the best bound available from the independent constraints (4): put S=√(W²+A²), u₀=RW/S, and u_{n,j}=RA a_{n,j}/(S q_j) for q_j>0; put u_{n,j}=0 if q_j=0. Each nonzero block saturates (4), and the weighted sum attains R S. This is sharpness for the finite fibre relaxation. It does not assert that these coordinates for different y arise from one autocorrelation.

For nonnegative a, the Euclidean norm of each block is at most its sum; hence 0≤A≤B. Consequently √(W²+A²)≤W+A≤W+B, yielding 0≤K≤B. Rationalizing the difference of square roots proves (2), since the denominator is at least 2W.

Every E_n lies above δ: log n−δ≥log 2−δ=δ. Since w is continuous on [δ,L] and there are finitely many nodes, all a, A, B and K are bounded. The shares satisfy 0≤ρ_n≤1 and are measurable, so these functions are measurable. Thus K is Lebesgue integrable even though W itself is not integrable at zero. In particular, one must not separate ∫W from ∫√(W²+A²).

Integrate (5). All energy terms are nonnegative, allowing Tonelli without a finite-energy assumption. The two affine substitutions x=log n±y, each with absolute Jacobian 1, give the exact identity

\[
 \sum_{n,\sigma}\int_0^\delta
    a_{n,\sigma}(y)D(\log n+\sigma y)\,dy
 =\int_{\cup_n E_n}w(x)D(x)\sum_n\rho_n(x)\,dx. \tag{6}
\]

Removing the finite set of centres and endpoints changes no Lebesgue integral. The physical capacity Σρ_n≤1 and disjointness of (0,δ) from all E_n bound the integral of the right side of (5) by the energy on (0,L). This proves (1).

Finally y w(y)→1 as y↓0 follows from exp(y/2)→1 and sinh(y)/y→1. Bounded A and (2) give 0≤B−K=O(y). This makes the origin-singularity transfer quantitative without differentiating h.

## An explicit allocation covering the whole interval

Put M(x)=Σ_{n=2}^N 1_{E_n}(x) and ρ_n(x)=1_{E_n}(x)/M(x), with 0/0 defined as 0. These are measurable because M is a finite sum of interval indicators. On the union of collars, Σρ_n=1.

The union is exactly (δ,L). For N=2 this is immediate. For successive centres, log(n+1)−log n<log 2=2δ when n≥2, so consecutive open collars overlap; their union starts at log 2−δ=δ and extends beyond log N. Intersecting with (0,L) gives (δ,L). Thus (6), plus the origin integral, equals the full energy, not merely a restricted subinterval energy.

This construction yields a completely specified coefficient in (1), using only N, logarithms, w, interval indicators, finite sums and square roots. It is a feasible physical allocation. Optimality in (3) is for the origin shares at fixed ρ; global optimization over ρ is a distinct problem and is not claimed here.

The coefficient is strictly positive: the left collar of n=2 contains points log 2−y for every 0<y<δ and has strictly positive equal-multiplicity density. Therefore A>0 and B>0 everywhere on this y interval. Since W>0, √(W²+A²)<W+A≤W+B, hence K>0. A positive measurable function on an interval of positive length has positive integral.

## Capacity saturation is necessary for physical optimality

There is a further exact restriction on the remaining optimization over ρ: any allocation leaving unused capacity on a set of positive Lebesgue measure can be strictly improved.

Fix a fibre and increase its nonnegative coefficient vector a by a nonnegative vector b with total mass d>0. Write A for the old sum of block norms and A' for the new one. The triangle inequality gives A'≤A+d. Therefore, for W>0,

\[
 K(W,a+b)-K(W,a)
 \ge d-\left[\sqrt{W^2+(A+d)^2}-\sqrt{W^2+A^2}\right]>0.
\]

Indeed the square-root difference is
`d(2A+d)/(sqrt(W²+(A+d)²)+sqrt(W²+A²))`, whose denominator is strictly larger than `2A+d`. The same argument gives nondecrease when d=0.

For a physical subpartition, assign all missing mass `1−Σρ_n(x)` to the least-indexed collar containing x. This is a measurable completion because there are finitely many measurable collars. It increases every pulled-back coefficient weakly. If the physical deficiency set has positive measure, some assigned collar receives a positive increase on a positive-measure set; one of its two affine branches pulls that set back to a positive-measure subset of `(0,δ)`. On that subset the preceding fibre inequality is strict. The coefficient integrals are finite, so integrating gives a strict increase in `∫K`.

Consequently the supremum over subpartitions equals the supremum over partitions, and every maximizer, if one exists, saturates `Σρ_n=1` almost everywhere on `(δ,L)`. This does not prove existence or identify the maximizing partition. It removes unused physical capacity as a possible feature of an optimizer.

## Precision and open work

- Independent origin allocations must be indexed by both coset and sign.
- The block norm is Σ_j ||a_j||₂. Replacing it by ||a||₂ assumes cross-coset orthogonality that the grid does not provide.
- Optimal origin splitting is exact; the equal-multiplicity physical allocation need not be globally optimal.
- The relaxed finite-dimensional extremizer need not be a globally realizable positive-definite correlation.
- Paper proof above is complete. Lean audit status is recorded in the pipeline card; paper claims are not automatically Lean claims.
- [CollarAllocationDuality.md](CollarAllocationDuality.md) now proves a measurable dual certificate
  and exact global comparison remainder on paper. A zero certificate proves optimality;
  existence of a partition with such a certificate and the role of fractional splitting remain open.

## Formal theorem scope

`IntegratedOriginCollarLeverage.lean` assembles the explicit equal-multiplicity specialization
for `N=n+2`. Its source type `LogarithmicGridSource n` consists of compactly supported
continuous real functions whose autocorrelations vanish at the literal nodes log 2 through
log(n+2). These are admissibility conditions, not assumed estimates. No differentiability
or finite-energy hypothesis is required.

The endpoint `integrated_logarithmic_origin_collar_real_bound` states

`ENNReal.ofReal (logarithmicCollarRealConstant n * autocorr f.1 0) ≤ full extended energy`.

The coefficient is the ordinary real Lebesgue integral of K. Separate results prove its
integrability and strict positivity, and prove the measurability and exact optimality of
the displayed origin shares. The right side remains an extended nonnegative integral,
so the theorem also covers sources with infinite energy. The working ledger records
the final source and axiom audit status.

The paper theorem above allows arbitrary continuous real positive-definite kernels and
general measurable physical subpartitions. That broader domain, the capacity-saturation
theorem, uniqueness of the optimal origin share, and the `O(y)` defect estimate remain
paper-only. The Lean endpoint does not claim global optimality of equal-multiplicity
physical shares or realization of the fibre extremizers by one autocorrelation.
