# All-length Heath–Brown closure by dilation beyond the balanced scale

- **ID:** heath-brown-all-length-dilation-closure
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
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

## Sharp all-k S₂ consequence

Fix a smooth bump w, an integer k≥1, and 0<ε≤1. For T≥2, 1≤N≤T, and
a nonempty T^ε-separated W⊆[0,T], the single-block reduction gives

`|S₂| ≤ C₆₁ T^(6ε) (N²/M₀) X`,

where M₀=2^j≤(2T)^(1+ε)/N+1 and X is the unit-coefficient pair sum on
the selected dyadic segment. The block j=0 is contained in {1}, so its
contribution is at most `C₆₁ T^(6ε) N²R²`.

For j≥1 put A=M₀-1, B=2M₀-1, P=A^k, and m=2k. Then A≥1,
B≤3A, and B^k≤2^mP. The existing power lift gives

`X^k ≤ R^(2k-2) D^(2k) Y`,

where Y is the unit pair sum on (A^k,B^k] and D bounds the divisor
function there. Positive-kernel support domination and the dyadic cover
bound Y by `8^m` times the new three-term Heath–Brown majorant at P.
In this section H denotes its uniform constant Cε, independent of T and
the block length. Since P≤M₀^k and P²≤M₀^(2k), this yields

`D^(2k)Y ≤ D^(2k)8^m H T^ε
  [R²M₀^k+R M₀^(2k)+R^(5/4)T'^(1/2)M₀^k]`,

with `T'=2(2T)^(1+ε)`, so M₀≤T'/N and T'≤8T·T^ε. The exact
three-term assembly `prop61_abstract` therefore gives the bracket

`N²R² + T'N R^(2-1/k) + N²R^(2-3/(4k)) T'^(1/(2k))`.

The middle exponent follows directly from the diagonal term R M₀^(2k);
the fourth term responsible for the older exponent is absent.

The auxiliary bound M₀≤8T² gives
`B^k≤32^(4k)T^(4k)`. Choose δ by `exists_blockConst_divisor_le` for
these fixed exponents. For one constant Cδ≥0, enlarged to dominate H,
`D²≤CδT^ε`. Since k≥1 and T^ε≥1,

`[D^(2k)8^(2k)H T^ε]^(1/k)
 ≤ 64 Cδ max(1,2Cδ) T^(2ε)`.

The bracket at T' is at most 8T^ε times its value at T. Combining this
with the first T^(6ε) gives a uniform C such that

`|S₂| ≤ C T^(9ε)
 [N²R² + TN R^(2-1/k) + N²R^(2-3/(4k))T^(1/(2k))]`.

For an arbitrary target ε>0, use e=min(ε/9,1). Separation at T^ε
implies separation at T^e, and T^(9e)≤T^ε. The empty set contributes
zero. This proves the exact `PropSixOneBound w k k` family. Applying
the existing unconditional S₃ bound through `propTwelveOne_of_S_bounds`
then proves the published Proposition 12.1 at every k≥1.

## Lean certificate status

The all-length proof is in
`formal/GaloisForLFunctions/RHTower/Sieve/HeathBrownPairSumAllLengths.lean`.
Its endpoint is `RHTower.GuthMaynard.heathBrownPairSumBound_holds`.
The full source and all seven public declarations passed the scratch leaf
check and transitive axiom audit, using only `propext`, `Classical.choice`,
and `Quot.sound`. The canonical leaf check passed and `RHTower.lean` imports
the module once. Commands, source hashes and axiom output are recorded in
`logs/just-work-2410/RHTower__Sieve__HeathBrownPairSumAllLengths.*`.
`RHTower/Sieve/GuthMaynardSharpSTwo.lean` proves the sharp all-k S₂ family
and Proposition 12.1. Its full source and all three public transitive axiom
audits passed, again with only the three standard axioms. Its canonical
final check passed and the owning umbrella imports it once. The exact
endpoints are `propSixOneBound_sharp` and `propTwelveOne_unconditional`.
Their evidence is in `logs/just-work-2410/RHTower__Sieve__GuthMaynardSharpSTwo.*`.

## Gates

- [x] Exact published theorem, all quantifiers fixed.
- [x] Paper proof without a missing analytic input.
- [x] Lean all-length estimate, uniform constant, and endpoint proposition.
- [x] Sharp all-k S₂ application and Proposition 12.1 input.
- [x] Canonical leaf checks, all public transitive axioms, umbrella imports.
