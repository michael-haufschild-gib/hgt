# An unconditional bounded source with increasing matched moments

**[BRIDGE K-growing-jet], paper proved; Lean pending.** This is an actual
coefficient construction, not the full chronological repair theorem [R].
No computational result or RH assumption enters the proof.

## Statement

There are real arrays a_(k,N), |a_(k,N)|≤1, and integers m_N→∞ such that,
for all sufficiently large N, with M=floor(N/2),

    a_(k,N)=μ(k) for 1≤k≤M,
    Σ_(k≤N) a_(k,N)/k=0,
    Σ_(k≤N) a_(k,N)=−2,
    Σ_(k≤N) a_(k,N)k^(2j−1)=−2j/B_(2j), 1≤j≤m_N.

Consequently the analytic residual at t=0 has zero constant and first m_N
odd derivatives; every positive even derivative remains 1. For each δ>0,
the actual residual converges to zero in L²([δ,∞)) and uniformly there.
No claim is made about its full L² norm on (0,∞).

## Construction and proof

For fixed m use the real functions v(x)=(x⁻¹,1,x,x³,…,x^(2m−1)) on
[1/2,1], omitting the positive powers when m=0. Let

    G_N=Σ_(M<k≤N) v(k/N)v(k/N)^T,
    b_N=τ_(m,N)−Σ_(k≤M) μ(k)v(k/N),
    τ_(-1)=0, τ_0=−2,
    τ_(2j−1)=−[2j/B_(2j)]N^(−(2j−1)).

Whenever G_N is invertible, set c_N=G_N⁻¹b_N and assign the tail
a_k=c_N^T v(k/N). These coefficients satisfy exactly the required scaled
moments, hence the unscaled moments as well. They uniquely minimize the
sum of squared tail coefficients: every other solution differs by a vector
orthogonal to the sampled v columns, so Pythagoras applies.

For fixed m, N⁻¹G_N→G=∫_(1/2)^1 v(x)v(x)^T dx. This matrix is positive
definite. A vanishing quadratic form would make a linear combination of v
zero on the interval; multiplication by x makes an identically zero polynomial
with distinct powers, so every coefficient is zero. Thus G_N is invertible
for all sufficiently large N and N G_N⁻¹ remains bounded.

The unconditional PNT consequences Mertens(X)=o(X) and Σ_(k≤X)μ(k)/k→0
give b_N/N→0. For the x⁻¹ coordinate the head divided by N is exactly the
harmonic Möbius sum. For exponent p≥0, Abel summation gives

    N⁻¹ Σ_(k≤M) μ(k)(k/N)^p →0.

For p=0 this is Mertens(M)/N→0. For p>0, write the sum as
N^(−p)[Mertens(M)M^p−∫₁^M Mertens(x)p x^(p−1)dx] and split the
integral into a fixed head and a tail bounded by η x. The target τ_(m,N)/N
also tends to zero. Hence c_N=(N G_N⁻¹)(b_N/N)→0. Since each component
of v is bounded on [1/2,1], the maximum absolute tail coefficient tends to
zero for every fixed m. In particular it is eventually at most one.

For each N, consider all m∈{0,…,N} whose displayed Gram matrix is invertible
and whose constructed tail lies in [−1,1]. If the set is nonempty, take its
largest m and the corresponding vector; otherwise set the whole row to zero
and m_N=0. Every fixed m is admissible eventually, so m_N→∞ and the
exceptional empty-set rows are finite. The head has |μ(k)|≤1, proving the
uniform unit budget. This finite admissibility definition uses exact real
mathematics; floating matrices in the experiment do not decide it in Lean.

## What is controlled in the physical variable

For t>0 put q=exp(−t). Absolute rearrangement of the divisor sum gives

    Σ_(k≥1) μ(k)/(exp(kt)−1)=q.

Indeed the coefficient of q^n is Σ_(k|n)μ(k), equal to 1 at n=1 and
zero otherwise; absolute convergence follows from |μ(k)|≤1 and a geometric
bound. Zero harmonic charge gives r_N=q−Σ_(k≤N)a_k/(exp(kt)−1).
The exact Möbius head and unit coefficient bound therefore yield

    |r_N(t)| ≤ 2 q^(M+1)/(1−q)².                           (B)

For t≥δ>0, this is at most 2 exp(−(M+1)t)/(1−exp(−δ))², and thus

    ||r_N||_(L²([δ,∞)))
      ≤ sqrt(2) exp(−(M+1)δ) / [(1−exp(−δ))² sqrt(M+1)].

This proves the stated local-away-from-zero convergence with an explicit
bound. It does not control a cutoff δ_N→0 without comparing its rate with M.

## Exact gap and positive consequence

The construction supplies coefficient control, exact arithmetic prefix,
charge cancellation and increasing jet order simultaneously. Their conjunction
still has no proved full-norm limit. Fixed-m failure is proved on paper in
[the finite-tail boundary](chronological-finite-tail-obstruction.md).

The diagonal argument gives no quantitative lower bound for m_N. It cannot
be substituted into a remainder estimate requiring m_N≥c log N. Even such
a rate would initially control only t below the Taylor radius 2π/N; the
remaining interval approaching zero must also be estimated. The unresolved
task is the actual N-dependent small-t remainder, not existence of finite
moment solutions or a uniform coefficient budget by itself.

Lean work must formalize this exact source construction, PNT transfer and
bound (B), in addition to the fixed-space obstruction. Neither paper is
currently a Lean capstone or an RH proof. No novelty claim is made.
