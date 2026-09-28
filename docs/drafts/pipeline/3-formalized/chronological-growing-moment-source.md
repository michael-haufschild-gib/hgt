# An unconditional bounded source with increasing matched moments

**[BRIDGE K-growing-jet], Lean-complete (Stage 3-formalized).** Every proven
statement below (construction, jets, bounds (B)/(C), logarithmic window and
its equivalence with [R] for these rows, the coth remainder and its bounds, and
identities (D)/(E)) is proved in Lean; axioms `propext`, `Classical.choice`,
`Quot.sound` only. This is an actual coefficient construction, not the full
chronological repair theorem [R]. No computational result or RH assumption
enters the proof.

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
The jets refer to the right-hand analytic extension h(0)=1/2. The corpus's
positive-half-line function assigns a different value at zero; a Lean jet
theorem must define this extension explicitly. Positive-t values and L²
norms are unaffected.

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

Existing corpus sources for these arithmetic inputs are
`RHTower.deningerHarmonicPartial_tendsto` in `DeningerHarmonicPartial.lean`,
`RHTower.deningerHarmonicLimit_eq_zero` in `DeningerMobiusHarmonicZero.lean`,
and `deningerMertensM_log_pow_four_rate` in `Sieve/MoebiusHarmonicLogRate.lean`.
These have been read as dependencies, not rebuilt or re-audited here.

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

## Shrinking logarithmic window [BRIDGE K-window]

For the same zero-charge, unit-bounded half-prefix rows, put K=M+1. Keeping
the two geometric denominators separate improves (B) to

    |r_N(t)| ≤ 2 exp(−Kt)/[(1−exp(−t))(1−exp(−Kt))].       (C)

Indeed 1−exp(−kt)≥1−exp(−Kt) for every k≥K, and the numerator sums
as an ordinary geometric tail. Let N≥4 and δ=log(N)/N. Then 0<δ≤1,
K≥N/2, exp(−Kδ)≤N^(−1/2)≤1/2, and
1−exp(−δ)≥δ/(1+δ)≥δ/2. The first inequality follows from exp(δ)≥1+δ.
For every t≥δ, (C) is consequently bounded by 8 exp(−Kt)/δ. Integration
gives

    ∫_δ∞ |r_N(t)|²dt ≤ 64 exp(−2Kδ)/(2K δ²)
                      ≤ 64/[N² δ²] = 64/(log N)².

Thus ||r_N||_(L²([log(N)/N,∞)))≤8/log(N). No PNT or moment constraint
is needed for this bound beyond the stated exact Möbius head and zero charge.

Consequently, for the constructed growing-jet source, full [R] is equivalent
to the single remaining actual-source estimate

    N⁻¹ ∫₀^(log N) |r_N(u/N)|²du →0.

This follows by splitting the squared norm at δ and substituting u=Nt.
The interval in rescaled time grows; replacing it by a fixed compact interval
would weaken the claim and would not complete [R]. This bound and the
equivalence are Lean-complete.

## Exact gap and positive consequence

**Exact remainder attack and surviving local bound.** The classical
[coth partial fractions, DLMF 4.36.3](https://dlmf.nist.gov/4.36.E3) give

    h(z)=1/2−2z Σ_(n≥1) 1/[z²+(2πn)²],  z>0.

After the odd polynomial through degree 2m−1 is removed, the exact remainder is

    R_m(z)=(-1)^(m+1) 2 z^(2m+1)
              Σ_(n≥1) 1/[(2πn)^(2m)(z²+(2πn)²)].

This is a finite geometric identity inside an absolutely convergent series;
it is valid for all positive z. The integral comparison ζ(2m+2)≤2 gives
|R_m(z)|≤4 z^(2m+1)/(2π)^(2m+2). For a unit row with the displayed
constant and odd moment constraints,

    r_N(t)=cosh(t)−1−[sinh(t)−Σ_(j=1)^m t^(2j−1)/(2j−1)!]
                         +Σ_(k≤N)a_k R_m(kt).

For 0≤u≤1, t=u/N, Taylor's integral remainder for exp and cosh yields

    ||r_N||_(L²([0,1/N)))
      ≤ exp(1)/(2 sqrt(5) N^(5/2))
        + exp(1)/[(2m+1)! sqrt(4m+3) N^(2m+3/2)]
        + 4 sqrt(N)/[(2π)^(2m+2) sqrt(4m+3)].

The last term is the cost of taking absolute values before summing the
arithmetic coefficients. The diagonal source proof supplies no rate on m_N
that makes even this local majorant vanish. For instance a sufficient rate
for this term is m_N−log(N)/(4 log(2π))→+∞, but it has not been proved for
the constructed source.

On 0≤u≤log N the corresponding arithmetic remainder majorant is

    4 sqrt(N) (log N)^(2m+3/2) /[(2π)^(2m+2) sqrt(4m+3)].

When log N is large this increases with m, so that absolute Taylor estimate
cannot prove the required full-window limit. This is a failure of the bound,
not a lower bound on the actual signed remainder. The positive residue is
the exact remainder formula and the proved local upper bound above; both are
Lean-complete, and the source family is not retired.

The construction supplies coefficient control, exact arithmetic prefix,
charge cancellation and increasing jet order simultaneously. Their conjunction
still has no proved full-norm limit. Fixed-m failure is proved, and Lean-complete, in
[the finite-tail boundary](chronological-finite-tail-obstruction.md).

The diagonal argument gives no quantitative lower bound for m_N. It cannot
be substituted into a remainder estimate requiring m_N≥c log N. Even such
a rate would initially control only t below the Taylor radius 2π/N; the
remaining interval approaching zero must also be estimated. The unresolved
task is the actual N-dependent small-t remainder, not existence of finite
moment solutions or a uniform coefficient budget by itself.

The source construction, PNT transfer, bounds (B)/(C) and the logarithmic
window are Lean-complete, as is the fixed-space obstruction. Neither result is
an RH proof. No novelty claim is made.

## Exact signed projection formula and the harmonic channel

**[BRIDGE K-signed-projection], Lean-complete.** Keep the same
coefficients, not a replacement family. For any N≥2 and admissible m, put
x_k=k/N, θ_N=M/N and, for u>0,

    z_N(u)=Σ_(M<k≤N) v(x_k) h(u x_k),
    d_N(u)=G_N⁻¹ z_N(u),
    q_N(u,x)=v(x)^T d_N(u),
    Ψ_N(u)=exp(−u/N)+τ_(m,N)^T d_N(u).

The actual residual satisfies the finite identity

    r_N(u/N)=Ψ_N(u)+Σ_(k≤M) μ(k)[h(u x_k)−q_N(u,x_k)].       (D)

Indeed, G_N and its inverse are symmetric, so the actual tail sum is
c_N^T z_N=b_N^T d_N=τ^T d_N−Σ_(k≤M)μ(k)v(x_k)^T d_N.
Adding the head and target proves (D), with no limiting interchange.
The function q_N is the least-squares projection of h(u·) on the actual
tail samples. Its use at head points is extrapolation, not a contraction.

There is an additional endpoint issue: q_N generally has an x⁻¹ term.
Write d_(-1), d_0, d_j for its coordinates and define the regular kernel

    Φ_N(u,x)=h(ux)−d_0(u)−Σ_(j=1)^m d_j(u)x^(2j−1),
    H_M=Σ_(k≤M) μ(k)/k,
    A(y)=Σ_(1≤k≤y) μ(k).

Use h(0)=1/2 here. For fixed N,m,u the function Φ_N(u,·) is C¹ on
[0,θ_N]. Finite Abel summation gives the exact decomposition

    r_N(u/N)=Ψ_N(u)−N H_M d_(-1)(u)
      +A(M) Φ_N(u,θ_N)
      −∫₀^(θ_N) A(Nx) ∂_x Φ_N(u,x) dx.                    (E)

To check it, subtract d_(-1)/x from the head kernel in (D): its sum is
exactly −N H_M d_(-1). Apply summation by parts to the remaining smooth
kernel. The counting function A(Nx) is zero below 1/N, so the displayed
integral has no endpoint singularity. All terms in (E) belong to
L²([0,log N],du) for each fixed admissible row; the Gram inverse is finite
and the heat kernel has its analytic extension on this compact set.

Thus the hard estimate is exactly that the L² norm of the **joint right
side of (E)** is o(sqrt N) on this growing u-interval. The logarithmic-window
bound (C) then gives [R] for these rows. Splitting into absolute bounds
loses another cancellation: the normalized harmonic channel alone costs

    sqrt(N) |H_M| ||d_(-1)||_(L²([0,log N])).

Unconditional H_M→0 supplies neither a compensating square-root rate nor
control of d_(-1) as m grows. Likewise A(y)=o(y) in the regular Abel term
leaves a growing projection-variation factor. These facts identify the gap
in this proposed proof; they are not lower bounds or a refutation of (E),
the source family, or [R]. The signed harmonic and regular terms must be
estimated together, or a new quantitative estimate must control their costs.

## Lean formalization

All modules in `formal/GaloisForLFunctions/RHTower/`, wired into `RHTower.lean`.

| Card statement | Lean declaration | Module |
|-|-|-|
| Unit rows, `m_N → ∞`, prefix `μ(k)` for `k ≤ ⌊N/2⌋`, `Σ a/k = 0`, `Σ a = -2`, `Σ a k^(2j-1) = -2j/B_(2j)` (`j ≤ m_N`), eventually | `growingMomentSource_spec` | `ChronologicalGrowingMomentSource` |
| Jets at `t = 0` (value `0`, first `m_N` odd derivatives `0`, even derivatives `1`) with the analytic `h(0) = 1/2` | `growingMomentSource_jets`, `heatErrorExt_jets`, `iteratedDeriv_heatErrorExt_zero`, `iteratedDeriv_boseKernelE_zero` | `ChronologicalBoseKernelJets` |
| Uniform and `L²([δ,∞))` convergence for every `δ > 0` | `growingMomentSource_tendsto_away_from_zero` | `ChronologicalGrowingMomentSource` |
| Gram construction `c_N = G_N⁻¹ b_N`, exact scaled moments | `gmCoeff`, `gmRow`, `sum_gmRow_mul_gmVec`, `gmRow_moments` | same |
| Unique least-coefficient-norm tail (Pythagoras) | `sum_sq_tail_eq_add`, `gmTail_leastSquares` | same |
| `N⁻¹ G_N → G`, `G` positive definite, `G_N` invertible and `N G_N⁻¹` bounded | `tendsto_gmGramDisc`, `gramQuadForm_gmGramLim_pos`, `exists_gmGramDisc_coercive`, `exists_gmGram_inverse_bound` | `ChronologicalHalfTailGram`, `ChronologicalGrowingMomentSource` |
| `b_N/N → 0` (PNT: Mertens `o(X)`, harmonic sum `→ 0`, Abel summation) | `tendsto_gmRhs_div`, `tendsto_halfPrefix_moebius_pow`, `tendsto_halfPrefix_moebius_harmonic`, `abs_sum_Ioc_mul_le_of_monotone` | `ChronologicalMobiusHalfPrefixMoments` |
| `c_N → 0`, tail coefficients `→ 0` uniformly, every fixed `m` eventually admissible | `tendsto_gmCoeff`, `eventually_abs_gmTail_le`, `eventually_gmAdmissible` | `ChronologicalGrowingMomentSource` |
| Diagonal order: largest admissible `m ≤ N`, finitely many exceptional rows | `gmOrder`, `tendsto_gmOrder`, `eventually_gmAdmissible_gmOrder` | same |
| `Σ μ(k)/(e^(kt)−1) = e^(−t)`; zero charge gives `r_N = q − Σ a_k/(e^(kt)−1)` | `hasSum_moebius_div_exp_sub_one`, `heatError_eq_of_zeroCharge` | `ChronologicalZeroChargeTailBounds` |
| Bounds (C), (B), explicit `L²([δ,∞))` norm bound, uniform bound | `abs_heatError_le_of_zeroCharge`, `abs_heatError_le_of_zeroCharge'`, `sqrt_integral_sq_heatError_Ioi_le_of_zeroCharge`, `abs_heatError_le_of_zeroCharge_of_le` | same |
| Logarithmic window `‖r_N‖_(L²([log N/N,∞)))² ≤ 64/(log N)²` | `integral_sq_heatError_Ioi_log_le_of_zeroCharge`, `growingMomentSource_logWindow` | same, `ChronologicalGrowingMomentSource` |
| [R] for these rows ⇔ `N⁻¹∫₀^(log N) r_N(u/N)² du → 0` | `tendsto_L2Norm_iff_logWindow_of_zeroCharge`, `growingMomentSource_L2_iff_window` | same |
| Coth partial fractions (DLMF 4.36.3) | `hasSum_bose_partial_fraction` (from mathlib `cot_series_rep'`) | `ChronologicalBoseCothRemainder` |
| Exact remainder `R_m`, `h = 1/2 − Σ B_(2j) z^(2j−1)/(2j)! + R_m`, `|R_m(z)| ≤ 4z^(2m+1)/(2π)^(2m+2)` | `boseRemainder`, `fusionBoseDefect_eq_taylor_add_remainder`, `abs_boseRemainder_le` | same |
| `r_N = cosh t − 1 − [sinh t − Σ …] + Σ a_k R_m(kt)` | `heatError_eq_cosh_sinh_remainder` | same |
| Local bound on `[0,1/N)` (three explicit terms) | `sqrt_integral_sq_heatError_local_le` | `ChronologicalBoseCothLocalBounds` |
| Sufficient rate `m_N − log N/(4 log 2π) → ∞` kills the third term | `tendsto_local_arith_term_of_rate` | same |
| Window majorant `4√N (log N)^(2m+3/2)/((2π)^(2m+2)√(4m+3))`, increasing in `m` for large `log N` (`≥ 4π`) | `sqrt_window_absArithRemainder_le`, `logWindowMajorant_le_succ` | same |
| Signed projection identity (D) | `heatError_gmRow_signed` | `ChronologicalGrowingSignedProjection` |
| Abel decomposition (E) with `h(0) = 1/2` | `heatError_gmRow_abel` | same |
| All terms of (E) in `L²([0, log N])`; harmonic-channel cost `√N |H_M| ‖d_(−1)‖` | `abel_terms_memLp`, `harmonic_channel_norm` | same |

**Verification.** `lake env lean` on each of the eight modules: clean.
`lake --old build` of the top modules: passed. `#print axioms` for 29 capstones:
only `propext`, `Classical.choice`, `Quot.sound`. No heartbeat options, no
numerical input. The open [R] estimate is untouched; nothing above claims it.
