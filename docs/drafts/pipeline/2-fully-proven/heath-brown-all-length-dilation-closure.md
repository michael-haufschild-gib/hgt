# All-length Heath–Brown closure by dilation beyond the balanced scale

- **ID:** heath-brown-all-length-dilation-closure
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Source:** review-2410 J3; Guth–Maynard Theorem 1.6.
- **Statement:** `HeathBrownPairSumBound` holds with its constant chosen before
  the separated set, interval, coefficients, and unrestricted block length.
- **Scientific status:** Published theorem; formalization bridge, no novelty claim.

## Exact target

For each ε>0 there is Cε≥0 such that every 1-separated finite W in an
interval of length T≥2, every integer M≥1, and every |a(n)|≤1 satisfy

`Σ_(s,t∈W) |Σ_(M<n≤2M) a(n)n^(i(s-t))|²`
`≤ Cε T^ε [R²M + RM² + R^(5/4) T^(1/2) M]`, where R=|W|.

Reference: [Guth–Maynard, Theorem 1.6](https://arxiv.org/html/2405.20552v2).

## Dependency-closed paper proof

Use the existing nonnegative ratio kernel and let A(S) be its weighted
pair sum at exponent 1/2. Write A(N)=A((N,2N]). The corpus supplies:

1. Arbitrary coefficient domination: P(M,a)≤2M A(M)
   (`hbPairSum_le_two_mul_hbAmp_half`).
2. Weighted-to-unit comparison: A(N)≤P(N,1)/N
   (`hbAmp_half_le_hbPairSum_div`).
3. Reflection, with H=hbSelfDualConst(T,δ), independent of N:
   for 2T<N²,
   `P(N,1)≤H[R²N+RN²+R^(5/4)√T N+R^(3/2)T]`
   (`hbPairSum_Ioc_le_reflected`).
4. Dilation: for 1≤M≤L and d(u)≤D on (L,4L],
   `A(M)≤2D A((L,4L])`
   (`hbAmp_half_le_of_le`, c=2).
5. Splitting into the two dyadic blocks costs at most twice their sum.
   This is `hbPairSum_union_le` applied to the weighted coefficients.
6. The divisor bound d(u)≤Cδ u^δ and the constant estimates in
   `exists_blockConst_divisor_le` and `one_add_logb_two_le_rpow`.

If R=0 the claim is immediate. Otherwise 1≤R≤T+1≤2T, by separation.
Set `G=√T R^(1/4)`, `P=RG=R^(5/4)√T`, and `L=ceil(2G)`.
Then G≥1, 2G≤L≤3G, L≥1, and 2T<L². Also G≤2T and L≤6T.

For N≥L, `R^(3/2)T=RG²≤RN²`. Reflection therefore gives

`P(N,a)≤2H [R²N+RN²+PN]`.

Here arbitrary coefficients are allowed directly in the reflection theorem.
This case includes arbitrarily large N; no N-dependent divisor bound is used.

For M<L, choose `D=Cδ (4L)^δ`, so the divisor bound applies to all
u in (L,4L]. Dilation and the two-block split give

`A(M)≤4D[A(L)+A(2L)]`.

For N=L or 2L, combine (2) and (3), then use G≤N≤6G:

`A(N)≤H[R²+RN+P+RG²/N]≤H[R²+13P]`.

Thus `P(M,a)≤16DH M[R²+13P]≤208DH[R²M+RM²+PM]`.
Both cases are bounded by `208(D+1)H` times the target majorant.
Replacing D by `D*=Cδ ceil(24T²)^δ` bounds this common factor uniformly
in W and M. This uses only the coarse bounds `G≤2T²` and `L≤6T²`;
the sharper bounds above are not needed for the constant estimate.

Choose δ and C from `exists_blockConst_divisor_le` with exponent ε/3,
a=64 and b=2. Every relevant auxiliary length is ≤64T²:
`hbLongBlock T≤4T`, `ceil(2T)²≤9T²`, and `ceil(24T²)≤25T²`.
Consequently the small/block constants and `(D*)²` are ≤C T^(ε/3).
The inequality D*≤(D*)²+1 gives D*+1≤(C+2)T^(ε/3).
The reflection factor is bounded by the block constant at zero, hence also
by C T^(ε/3). Finally

`(1+log₂T)³≤[1+9/(ε log 2)]³ T^(ε/3)`.

The definition of H now gives
`H≤[4C+7200000 C(1+9/(ε log 2))³]T^(2ε/3)`.
Multiplication proves the target with the absolute-in-data constant

`208(C+2)[4C+7200000 C(1+9/(ε log 2))³]`.

All ingredients are unconditional corpus theorems. This repairs the apparent
balanced-length gap by dilating *before* using the reflected estimate. The
auxiliary length depends on R, while its constants are bounded using R≤2T.

## Gates

- [x] Exact published theorem, all quantifiers fixed.
- [x] Paper proof without a missing analytic input.
- [ ] Lean all-length estimate, uniform constant, and endpoint proposition.
- [ ] Sharp all-k S₂ application and Proposition 12.1 input.
- [ ] Canonical leaf checks, all public transitive axioms, umbrella imports.
